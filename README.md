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
| constructive coverage call summary | 支持 | result-indexed inverse witnesses |
| 二选一 nondeterministic `choose` | 支持 | demonic upper / angelic lower |
| 反例模型、SMT-LIB 导出 | 支持 | Z3 / `--emit-smt` |
| safety 函数 summary、直接/互递归 | 支持 | call-graph SCC + `int` measure |
| 递归 coverage | 有条件支持 | complete witnesses + SCC measure |
| 开放 polymorphic ADT obligation、高阶值 | 明确拒绝 | 需要 finite instances/closure |
| functor、first-class/recursive module | 明确拒绝 | 需要 theory transformer/generativity |
| mutation、exception、algebraic effects | 明确拒绝 | 需要 relational outcome semantics |
| GADT、object、polymorphic variant | 明确拒绝 | 需要 feature-specific theory |
| Evar/Hindley/Horn/function-SCC/theory-slice fuzzing | 支持 | deterministic `@fuzz` + graph oracle |
| Generic result propagation | 支持 | ANF Let/Var、inlining、同型 branch merge |

未支持的 Typedtree node 会报错。

## 下一阶段

详细语义见 `docs/design.md`。推荐顺序：

1. 关系化 mutation、exception 和 effect handler；
2. parameterized abstract sorts 与 nested functor theory；
3. 可重放 proof certificate 与稳定 `.rmi` 格式。

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
