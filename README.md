# refinedOCaml

`refinedOCaml` 是一个把双向 refinement types 植入 OCaml 的研究原型：

- **over-approximation**：所有实际结果都满足后置条件，用来证明 safety/correctness；
- **coverage/under-approximation**：后置条件中的每个结果都确实可达，用来证明 coverage、
  reachability 或 incorrectness。

每个 ADT 默认编码为 uninterpreted sort；
constructor、recognizer 和 selector 都是 uninterpreted symbols，代数性质由可查看的 axioms 给出。

当前 versioned frontend 针对 OCaml 5.3.0；运行验证还需要 `z3` 可执行文件。

可复现环境：

```sh
dev/setup-switch.sh .
eval "$(opam env --switch=. --set-switch)"
dune build @refined
```

脚本使用 `refined_ocaml.opam.locked` 安装经过测试的直接依赖。CI 在 Ubuntu/OCaml 5.3.0 上安装
Z3，并运行 build、install、完整 refinement tests 和 formatting gate。compiler-libs 升级规则见
`docs/versioning.md`。

Property fuzz tests：

```sh
dune build @fuzz
REFINED_FUZZ_CASES=20000 REFINED_FUZZ_SEED=1592594470 dune build @fuzz --force
```

Fuzzer 默认使用固定 seed 跑 5,000 cases；CI 跑 20,000 cases。失败信息包含 seed 和 case index，
可以原样重放。

`autofix.ci` workflow 会在 pull request 和 `main` push 上运行 `dune fmt`，并把格式修复提交回来源
分支。仓库管理员需要先为该仓库安装 [autofix.ci GitHub App](https://autofix.ci/setup)；workflow
自身只申请 `contents: read`，上传修复时使用固定 commit 的官方 action。

## 当前 MVP

权威验证路径运行在 OCaml 普通类型检查之后：

```text
.ml → OCaml/PPX → Typedtree (.cmt/.cmti) → refined Core → SMT → Z3
```

因此 checker 使用的是 OCaml 已解析和实例化的 `Types.type_expr`、`Path.t`、`Ident.t` 以及
constructor/field UID。普通类型错误产生的 partial Typedtree 会被拒绝。

```ocaml
let[@refined.over { pre = "x >= 0"; post = "result > x" }]
    succ (x : int) : int =
  x + 1

let[@refined.coverage { pre = "x >= 0"; post = "result >= 1" }]
    positive_range (x : int) : int =
  x + 1
```

编译并验证：

```sh
ocamlc -bin-annot -c examples/valid.ml
dune exec refined-ocaml -- examples/valid.cmt
dune exec refined-ocaml -- --emit-smt work/smt examples/valid.cmt
dune build @refined
```

CLI 只接受完成普通 OCaml typing 后生成的 `.cmt` implementation。

## PPX 的职责

`refined_ocaml.ppx` 检查 contract attribute 的形状，并刻意保留 attributes，使其进入 Typedtree：

```lisp
(preprocess (pps refined_ocaml.ppx))
```

## 两种 refinement

对纯函数 `f : X -> Y`：

```text
over     {P} f {Q} ≜ ∀x. P(x) ⇒ Q(x, f(x))
coverage [P] f [Q] ≜ ∀y. Q(y) ⇒ ∃x. P(x) ∧ y = f(x)
```

Coverage contract 描述函数 image 的一个下界。当前 coverage
`post` 只能引用 `result`。可选的 constructive witnesses 为每个参数给出只依赖 `result` 的 inverse：

```ocaml
let[@refined.coverage
      {
        pre = "x >= 0";
        post = "result >= 1";
        witnesses = [ ("x", "result - 1") ];
      }]
    successor x =
  x + 1
```

此时 checker 验证更强的 judgment：

```text
forall result. post(result) =>
  pre(witness(result)) /\ result = f(witness(result))
```

完整 witness contract 可以作为 under call summary。Caller existentially 选择 call result，并加入 callee
post 与 `actual_argument = witness(call_result)`；多层调用因而可以组合。递归 under-summary 还要求 SCC
内 measure 非负且严格下降。没有 witnesses 的旧 contract 仍按 whole-image existential VC 验证，但只
能 inline，不能关闭递归调用。

当 inverse 不是函数时，可以改用 relational witness：

```ocaml
let[@refined.coverage
      {
        pre = "true";
        post = "result >= 0";
        witness_relation = "x = result || x = 0 - result";
      }]
    absolute x =
  if x >= 0 then x else 0 - x
```

Relation 可引用普通参数、`result`/outcome `payload`、final-state target，以及 reference 参数的
`old_<name>`。`ghosts = [("inverse", "int")]` 会引入 existential ghost；sort 也可以是 `bool`、tuple、
list/option、用户单态或闭合参数化 ADT，以及已导入的 abstract sort。同一 ghost 在 relation 和 functional
state witness 中可复用。Checker 分别证明 relation 对每个目标具有 witness（totality），
以及每个满足 relation 的 input/ghost 都执行到该目标（pointwise soundness），因此可安全用于 under call
summary。

验证器把 safety 反例和 coverage 的缺失结果交给 Z3：`unsat` 表示 contract 成立；`sat` 时输出
model。

## 同一个函数的 upper/lower bounds

同一 binding 可以同时声明 safety 和 coverage：

```ocaml
external choose : int -> int -> int = "refined_choose" [@@refined.choose]

let[@refined.over
      { pre = "true"; post = "result = 0 || result = 1" }]
   [@refined.coverage
      { pre = "true"; post = "result = 0 || result = 1" }]
    bit (_unit : unit) : int =
  choose 0 1
```

如果实现改成恒定返回 `0`，safety 仍成立，但 coverage 会报告 `missing_result = 1`。
`refined.under` 是 `refined.coverage` 的兼容别名。

`choose` alternatives 可以包含 heap writes、raise 或 perform。Frontend 保留两个 computation，不会按
OCaml 普通函数实参规则预先顺序求值；Safety 将 path union 解释为 demonic choice，Coverage 将其解释为
angelic reachability。

## Module theories 与 separate compilation

Module signature 可以导出 uninterpreted predicates 和 trusted axioms：

```ocaml
val mem : 'a list -> 'a -> bool [@@refined.predicate]
val hd : 'a list -> 'a -> bool [@@refined.predicate]

[@@@refined.axiom
  {
    name = "hd_mem";
    vars = [ ("l", "'a list"); ("x", "'a") ];
    body = "implies (hd l x) (mem l x)";
  }]
```

从 `.cmti` 生成带 `.cmi` digest 的 refinement interface：

```sh
refined-ocaml --emit-rmi list_theory.rmi list_theory.cmti
refined-ocaml --theory list_theory.rmi client.cmt
```

客户端只能获得 `.mli/.rmi` 导出的 theory。验证结果会列出
本次信任的用户 axioms；过期或不属于客户端 imports 的 `.rmi` 会被拒绝。

这里的 `'a` 在每个 obligation 中根据 Typedtree use-site type 实例化；例如两个客户端会分别得到
`mem$int : int list × int → Bool` 和 `mem$bool : bool list × Bool → Bool`。

`axiom` 属于 trusted computing base。签名还可以声明 checked lemma：

```ocaml
[@@@refined.lemma
{
  name = "not_mem_not_hd";
  vars = [ ("l", "'a list"); ("x", "'a") ];
  body = "implies (not (mem l x)) (not (hd l x))";
}]
```

`--emit-rmi` 会按声明顺序，以 trusted axioms 和先前已检查 lemmas 为上下文为每条 lemma 生成 VC。
只有全部得到 `unsat` 才会原子替换目标 `.rmi`；`sat` 或 `unknown` 都不会留下新 artifact。`.rmi` v3
分别保存 trusted axioms、checked lemmas，以及包含 VC digest、Z3 identity、timeout 和依赖列表的
verification artifact。客户端诊断也分别列出两类 provenance。

这里的 artifact 是可审计的验证记录，不是可由小型 kernel 独立重放的 Z3 proof certificate；solver
调用仍属于当前 checker 的可信边界。

### Abstract type theory 与 module alias

签名中的单态抽象类型会导出为作用域化 uninterpreted sort：

```ocaml
type t
val holds : t -> bool [@@refined.predicate]

[@@@refined.axiom
{ name = "holds_all"; vars = [ ("x", "t") ]; body = "holds x" }]
```

Axiom/lemma sort parser 按 lexical module scope 解析 `"t"`，并与 Typedtree 中客户端看到的
`Module.t` 使用同一个 sort identity。`.rmi` v5 显式保存这些 abstract sorts。

Structure 和 signature 中的 applicative module alias 也会保存为 theory path rewrite。Lookup 使用最长
前缀并递归展开 alias chain，因此客户端本地 `Local.holds` 可以依次解析到
`Abstract_theory.Alias.holds` 和 `Abstract_theory.Core.holds`。这只是别名，不处理 functor application、
generativity 或 destructive substitution。

### Functor theory transformer

Signature 中的一阶 theory functor 可以导出 predicates、trusted axioms 和单态 abstract result sorts。
应用 `Make(Arg)` 时，result theory 克隆到目标 module path，并注入 `Target.X -> Arg` 参数 alias；axiom
中的 `X.p` 因而连接到实际 argument theory。

具名参数 functor 使用 applicative identity：重复 `Make(Arg)` 共享 `Make(Arg).t`，不同 argument path
得到不同 sorts。Unit functor `Fresh()` 使用 application target path 生成 fresh sort，因此两次应用互不
相等。`.rmi` v5 保存 functor templates；theory slicing 会跨参数/result statements 求闭包。

当前只支持 identifier argument、signature result、具名一阶参数或 unit 参数。Functor result 中的
checked lemma、nested/first-class functor、匿名 module argument、`with type` destructive substitution
会 fail closed 或不导出 transformer。

### Hindley generic schemes

Module signature 可以导出 higher-sorted Hindley generic：

```ocaml
val complement : int -> int
[@@refined.hindley
  {
    generics = [ ("property", "int -> bool") ];
    parameters = [ ("Predicate", "int -> bool", "property", "true") ];
    result =
      ( "Predicate",
        "int -> bool",
        "fun value -> not (property value)",
        "true" );
  }]
```

调用点给出实参当前的 refinement type，而不是 generic instantiation：

```ocaml
List_theory.complement
  (value
  [@refined.type
    {
      base = "Predicate";
      sort = "int -> bool";
      index = "fun item -> item > 0";
      predicate = "true";
    }])
```

Checker 根据 parameter index 自动求出 `property`，对 result 做替换和 beta-reduction，并验证 generic
parameter 的 refinement precondition。`.rmi` 保存 scheme，CLI 显示求得的 ghost instantiation。缺少
`[@refined.type]`、未解 evar、类型不匹配或非 first-order constraint 都会拒绝验证。

Elaborated result refinement 会沿 ANF `let`、变量引用、局部 first-order inlining，以及 refinement
一致的 `if`/`match` 分支继续传播。因此 generic 调用链只需在第一个无法推导的来源值上写
`[@refined.type]`，后续调用会自动使用前一次调用的 result refinement。

`[@@refined.horn]` 使用相同 scheme surface，但 generic application 只能出现在 predicate 的顶层合取
中。调用点从 `assumption ⇒ property(index)` 收集 lower bounds，将 index 抽象为 lambda 参数，并把多条
lower bounds 合成析取。Horn application 位于 `not`、`or`、关系式内部或 datatype index 时会在 `.rmi`
生成阶段被拒绝。Horn predicates 会构成 dependency graph 和 SCC，从 `false` 开始同步迭代 least
fixpoint；互递归 SCC 支持 base-fact propagation，无依据循环稳定为 `false`，超出迭代上限则拒绝。
当前没有 widening，也不声称能求解超出受支持 term algebra 的任意 SMT-CHC。

## 函数 summary 与递归

带 `refined.over` 合约的本地一阶函数可作为 summary 使用，不再必须展开函数体。递归函数还要选择
一个 `int` 参数作为 well-founded measure：

```ocaml
let[@refined.over { pre = "n >= 0"; post = "result = 0" }]
   [@refined.measure "n"] rec countdown n =
  if n = 0 then 0 else countdown (n - 1)
```

Stable Core 会构造函数调用图并用 Tarjan 算法求 SCC。SCC 内每条调用边都使用 callee 的唯一 safety
summary，并在实际控制流路径下检查 summary precondition、caller measure 非负以及 callee measure
严格下降。每个带合约的 SCC 成员仍会独立产生 VC，因此 summary 不是 trusted axiom。

当前 measure 必须直接命名一个 `int` 参数。递归 coverage 只有在提供完整 constructive witnesses 时
才可使用 under-summary；whole-image existential contract 仍不能关闭递归调用。

## ADT 编码

例如：

```ocaml
type nat = Z | S of nat
```

产生形如：

```smt2
(declare-sort T_nat 0)
(declare-fun C_nat_Z () T_nat)
(declare-fun C_nat_S (T_nat) T_nat)
(declare-fun is_C_nat_Z (T_nat) Bool)
(declare-fun is_C_nat_S (T_nat) Bool)
(declare-fun sel_C_nat_S_0 (T_nat) T_nat)
```

自动 axioms 提供 recognition、cross-constructor exclusion、selector reduction、reconstruction 和
constructor coverage，从而得到 disjointness、injectivity 与 exhaustiveness。

默认**没有 induction axiom**，所以模型仍可能包含非标准或循环元素。需要归纳时必须通过
well-founded measure、checked lemma 或有限展开显式引入。

## Relational state/outcome semantics

Stable Core 现提供与 compiler-libs 无关的 relational algebra。每条 path 显式携带 guard、initial/final
state，以及三种 outcome：`Return value`、`Raised exception`、`Performed { operation; payload }`。

- `bind` 只继续 normal return paths，raise/perform 自动传播；
- `read`/`write` 对 ghost cell map 做显式 state threading；
- branch 保留 path guards；
- exception/effect handlers 只消除匹配的 abnormal outcomes；
- relational Safety 对所有可达 paths 检查对应 normal/raised/performed postcondition；
- relational Coverage 要求目标 outcome 至少匹配一个 guarded path。

该层位于 [relational_outcome.ml](src/relational_outcome.ml)，已经有 deterministic unit/property tests。
OCaml frontend 已支持 nullary exception、`raise E`、`try ... with E -> ...` 和 catch-all。Safety
contract 可增加 exceptional postconditions：

```ocaml
let[@refined.over
      {
        pre = "true";
        post = "result >= 0";
        raises = [ ("Negative", "x < 0") ];
      }]
    classify x =
  if x < 0 then raise Negative else x
```

Normal paths 检查 `post`，Raised paths 按异常名检查 `raises`；未列出的异常对应 `false`。单 payload
exception 已支持，predicate 可引用 `payload`；handler pattern `E payload` 会把实际 payload 绑定进 handler
Core。Coverage 用 `outcomes` 为 Raised/Performed paths 提供 constructive inverses。

Frontend 还支持局部 references：`let cell = ref init`、`!cell`、`cell := value`、sequence 和
条件分支。Safety contract 可为 normal outcomes 声明 final-state predicate：

```ocaml
let[@refined.over
      {
        pre = "true";
        post = "result = x + 1";
        state = [ ("cell", "value = result") ];
      }]
    bump x =
  let cell = ref x in
  cell := !cell + 1;
  !cell
```

`value` 表示该 path 的最终 cell 内容。Reference 参数的 `old` 是 function-entry content；局部
`let cell = ref init` 的 `old` 是 allocation-time `init`。State 会穿过 branch、raise 和 handler；因此
handler 可以观察异常发生前的写入。

Reference 参数作为 relational heap identities。`requires_state`约束 initial contents；Coverage 用
`state_witnesses`从目标 result/final cells 构造 initial contents：

```ocaml
requires_state = [ ("cell", "value >= 0") ];
state = [ ("cell", "value = result") ];
state_witnesses = [ ("cell", "result - 1") ];
```

每种 content sort 对应一个 SMT array heap，dereference/assignment 分别使用 `select`/`store`。
Safety/coverage call summaries 会把 callee final contents 更新回 caller heap；同一实际 identity 传给多个
ref formals 时生成 final-value consistency constraints。局部 `ref` 分配 fresh identity，并支持 lexical
alias。Pointer equality 与 reference 跨当前关系边界逃逸仍 fail closed。

Reference-parameter footprint 使用 `modifies = ["cell"]` 声明；`state` 中出现的 reference 会隐式加入
normal footprint。Raised/Performed paths 对应使用
`outcome_modifies = [("raise", "Bad", "cell")]`，`outcome_state` 同样会隐式加入。未列出的 reference
生成 frame obligation：只有当它不 alias 任一同 sort 的 modified identity 时，final content 必须等于
entry content。Safety 允许只有 `modifies`、没有 state predicate，此时 caller 对该 cell 做 havoc；Coverage
必须为每个 modified cell 提供 final-state target，防止 under-summary 凭空选择不可达状态。

异常与效果的 final heap 用 `outcome_state` 分别描述：

```ocaml
outcome_state = [
  ("raise", "Bad", "cell", "value = 1");
  ("perform", "Send", "cell", "value = payload");
]
```

Safety predicate 可引用 `value`、`old` 和可选 `payload`。Coverage 把这些内容作为对应 outcome 的 final
heap targets；跨函数 safety/under summaries 会在异常被 `try` 捕获或效果被 handler 处理之前更新 caller
heap。Pointer equality 与 reference 跨当前关系边界逃逸仍 fail closed。

OCaml 5.3 的标准 effect surface 通过 `Effect.perform` 与 `Effect.Deep.match_with` 提供。当前 frontend
支持 nullary operation 和 canonical abortive handler：

```ocaml
type _ Effect.t += Stop : int Effect.t

let[@refined.over
      {
        pre = "true";
        post = "result = 0";
        performs = [ ("Stop", "flag") ];
      }]
    run flag =
  if flag then Effect.perform Stop else 0
```

未处理的 Performed path 按 operation 名检查 `performs` predicate；未列出的 operation 失败。
`Effect.Deep.match_with (fun () -> body) () handler` 的 `effc` 可将匹配 operation 映射到 abortive
`Some (fun _continuation -> handler_body)`，或 one-shot resumptive
`Some (fun continuation -> Effect.Deep.continue continuation value)`。Handler tail 也可以用 `if` 在
Abort 与 Resume 间分支。Translator 使用 CPS 捕获 perform 后
的 computation；resumed continuation 再次 perform 时仍由同一个 deep handler set 处理，state 也会穿过
resumption。`retc` 必须是 identity，`exnc` 必须是 `raise`。

单 payload operation 和 conditional-linear continuation 已支持；`performs` predicate 与 handler
pattern 都可引用/bind `payload`。同一路径 non-tail 或顺序多次使用 continuation，以及非 literal handler
record仍 fail closed。OCaml Deep continuation 是 one-shot，verifier 不会把非法重复 `continue` 当成
multi-shot。

本地 effectful safety calls 可使用 outcome summary。Caller 为 callee normal result、exception payload、
effect payload 建立 fresh symbolic values，并产生 Return/Raised/Performed paths；Performed path 携带 caller
continuation，因此 caller 的 `try`/deep handler 可以跨函数边界处理 outcome。Callee precondition 作为独立
side obligation。跨函数 normal state summary 也会更新 caller cells。

Coverage contract 可为 abnormal outcomes 提供独立 constructive inverse clauses：

```ocaml
outcomes = [
  ("raise", "Bad", "payload < 0", [("x", "payload")]);
  ("perform", "Send", "payload = 0", [("x", "payload")]);
]
```

`post`/`witnesses` 或 `witness_relation` 描述 normal Return；每个 `outcomes` clause 描述目标
Raised/Performed payload 和 inverse。Outcome tuple 可增加第五个 relation 字符串。Whole-function VC
分别证明每类目标 outcome 可达；under call summary
existentially 选择 symbolic result/payload，并加入 actual-argument/witness equations。Performed summary
同时捕获 caller continuation。无 abnormal clauses 的旧 coverage 仍只检查 normal whole-image。

Effectful recursive summaries 使用与纯函数相同的 call-graph SCC 和 `[@refined.measure]`。Relational CPS
额外携带 source path conditions：Safety 只在实际递归分支证明 callee precondition、measure 非负和严格
下降；Coverage 把下降条件放入 constructive reachability guard。缺失 measure 会 fail closed。

参数化用户 ADT 会在每个 obligation 中按实际闭合类型实例化。例如 `'a box` 在两个不同使用点会
得到独立的 `T_box_Int` 与 `T_box_Bool` theory；constructor、recognizer、selector 和代数 axioms 的
名字也包含实例 sort，不会跨实例混用。递归参数化 ADT 会递归替换其 field sorts，多态一阶 helper
在 inline 时根据 Typedtree call-site types 实例化整个 Core body。

Checker 只为当前 obligation 及其 inline 调用实际出现的闭合实例生成 theory。仍含 `S_var` 的开放
ADT obligation 会 fail closed，因为它无法有限 monomorphise。同一 VC 可以在程序表达式中使用同一
constructor 的多个实例。

Contract 字符串在 OCaml parsing 后会 elaboration 成 compiler-independent 的 typed Logic AST。Equality
会双向传播 operand sort；constructor 从 expected result sort 和 argument sorts 选择实例；record field
从 receiver sort 选择 selector。因此同一 VC 中的 `result = Box x`、`Nothing = result` 和
`left.value`/`right.value` 可以分别解析到不同 ADT 实例。每个 Logic AST node 都带 sort，SMT translation
和 theory slicing 只消费 resolved symbols。真正没有任何类型信息的表达式（例如同时存在多个实例时的
`Nothing = Nothing`）仍会明确拒绝。

Theory 发射还会做 dependency-driven slicing。Roots 来自 contract、Core 中实际使用的
constructor/field/pattern、logic call 和 function summary；命中 statement 后，把该 axiom/lemma 中的
全部 symbols 加入闭包。Checked lemma 会同时保留 verification artifact 记录的 trusted 和 checked
dependencies。未使用的 logic declarations、statements、artifacts 和 ADT bundles 不进入 SMT；只有 ADT
sort 流过时把它当 opaque sort，不生成代数 axioms。无 named theory symbol 的全局算术 axiom 会被保守
切掉，除非被 artifact 显式依赖。

## 支持范围

| 特性 | 状态 | 编码 |
|---|---:|---|
| OCaml normal typing + use-site instantiation | 支持 | `.cmt` Typedtree |
| `int` / `bool`、算术、比较、布尔连接 | 支持 | SMT Int/Bool |
| `if`、简单局部 `let` | 支持 | `ite` / substitution |
| tuple | 支持 | uninterpreted product + selectors |
| 单态/参数化 variant、constructor、exhaustive `match` | 支持 | use-site monomorphisation + axioms |
| 单态/参数化 immutable record、字段读取 | 支持 | instance-specific constructor/selectors |
| 普通多态函数的 first-order 调用 | 支持 | Typedtree + inlining |
| module predicate/axiom/checked lemma 与 `.rmi` | 支持 | scoped FOL + verification artifact |
| 单态 abstract type theory / module alias | 支持 | scoped sort + alias-chain rewrite |
| applicative/unit functor theory | 支持 | parameter substitution + fresh unit results |
| dependency-driven theory slicing | 支持 | symbol/dependency least closure |
| typed Logic AST / expected-sort elaboration | 支持 | resolved constructor/selector symbols |
| over / coverage contract | 支持 | upper validity / lower image coverage |
| constructive coverage call summary | 支持 | functional/relational inverse witnesses |
| typed existential coverage ghosts | 支持 | primitives、tuple、closed ADT/abstract sorts |
| relational state/outcome semantic algebra | 支持 | guarded transition paths |
| stateful/outcome nondeterministic `choose` | 支持 | path union；demonic upper / angelic lower |
| 反例模型、SMT-LIB 导出 | 支持 | Z3 / `--emit-smt` |
| safety 函数 summary、直接/互递归 | 支持 | call-graph SCC + `int` measure |
| 递归 coverage | 有条件支持 | complete witnesses + SCC measure |
| 开放 polymorphic ADT obligation、高阶值 | 明确拒绝 | 需要 finite instances/closure |
| functor、first-class/recursive module | 明确拒绝 | 需要 theory transformer/generativity |
| nullary `raise`/`try` safety | 支持 | Return/Raised guarded paths |
| local refs / lexical alias / final-state safety | 支持 | per-sort SMT heap + fresh identity |
| nullary Effect.perform / abortive+one-shot Deep handler | 支持 | CPS continuation paths |
| conditional linear continuation | 支持 | guarded Abort/Resume actions |
| single-payload exception/effect | 支持 | payload-sorted outcome predicates |
| effectful safety call summary | 支持 | normal/Raised/Performed symbolic paths |
| exception/effect coverage summary | 支持 | per-outcome payload inverse witnesses |
| aliased reference parameters / state summaries | 支持 | identity select/store + consistency guards |
| abnormal outcome heap summaries | 支持 | `outcome_state` + caller heap update |
| heap footprint / frame clauses | 支持 | alias-aware `modifies` / `outcome_modifies` |
| pointer equality / escaping refs | 明确拒绝 | 需要 observable/first-class identity contracts |
| multi-payload/multi-shot handlers | 明确拒绝 | 需要 richer binders/continuation multiplicity |
| GADT、object、polymorphic variant | 明确拒绝 | 需要 feature-specific theory |
| Evar/Hindley/Horn/function-SCC/theory-slice fuzzing | 支持 | deterministic `@fuzz` + graph oracle |
| Generic result propagation | 支持 | ANF Let/Var、inlining、同型 branch merge |

未支持的 Typedtree node 会报错。

## 下一阶段

详细语义见 `docs/design.md`。推荐顺序：

1. first-class reference identity、pointer equality 与 escaping-reference discipline；
2. 可重放 proof certificate 与稳定 artifact 格式；
3. 显式 continuation cloning（若未来 OCaml API 支持）。

当前模块边界：

| 模块 | 职责 |
|---|---|
| `refined_ocaml.ir` | 不依赖 compiler-libs 的 source span、stable Core 与 VC semantics |
| `Ocaml_5_3_frontend` | 唯一接触 Typedtree/Types/Path/Ident/Shape/Cmt_format 的版本层 |
| `Vc_backend` | Core/logic 到 SMT obligation 的编码与 use-site specialization |
| `Solver_backend` | 有 timeout 的 Z3 process 与 verdict 解释 |
| `Refined_core` | 保持现有公共 API 的薄 façade |

IR 还导出 `Refinement_domain.S`、`Typing_judgment.Make` 与 `Evar_context.Make`。当前 Safety/Coverage
验证已经通过 compositional subsumption judgment 生成，而 use-site theory specialization 使用带
occurs-check 的 evar unifier。设计依据与后续 Hindley/Horn 边界见 `docs/generic-refinement-design.md`。

`Generic_refinement` 进一步提供 higher-sorted refinement terms、Hindley/Horn schemes 与 application
elaboration。Hindley generic 必须出现在 value-dependent input index；成功调用会返回显式 ghost
instantiations、替换后的结果类型和 argument subtyping constraints。
