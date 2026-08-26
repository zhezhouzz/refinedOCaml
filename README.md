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
`post` 只能引用 `result`；后续会加入 ghost variables 表达输入/输出状态关系。

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

目前 `axiom` 属于 trusted computing base。后续的 `lemma` 会先验证再导出。

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

## 支持范围

| 特性 | 状态 | 编码 |
|---|---:|---|
| OCaml normal typing + use-site instantiation | 支持 | `.cmt` Typedtree |
| `int` / `bool`、算术、比较、布尔连接 | 支持 | SMT Int/Bool |
| `if`、简单局部 `let` | 支持 | `ite` / substitution |
| tuple | 支持 | uninterpreted product + selectors |
| 单态 variant、constructor、exhaustive `match` | 支持 | uninterpreted sort + axioms |
| immutable record、字段读取 | 支持 | 单 constructor + selectors |
| 普通多态函数的 first-order 调用 | 支持 | Typedtree + inlining |
| module predicate/axiom 与 `.rmi` | 支持 | scoped FOL theory + digest |
| over / coverage contract | 支持 | upper validity / lower image coverage |
| 二选一 nondeterministic `choose` | 支持 | demonic upper / angelic lower |
| 反例模型、SMT-LIB 导出 | 支持 | Z3 / `--emit-smt` |
| 多态用户 ADT、高阶值、递归 | 明确拒绝 | 需要 monomorphisation/closure/measure |
| functor、first-class/recursive module | 明确拒绝 | 需要 theory transformer/generativity |
| mutation、exception、algebraic effects | 明确拒绝 | 需要 relational outcome semantics |
| GADT、object、polymorphic variant | 明确拒绝 | 需要 feature-specific theory |
| Evar/Hindley property fuzzing | 支持 | deterministic `@fuzz` + CI replay seed |

未支持的 Typedtree node 会报错。

## 下一阶段

详细语义见 `docs/design.md`。推荐顺序：

1. 加入 Horn generic constraint syntax、positivity checking 和 solver；
2. 将 Hindley result refinements 继续传播给后续表达式，减少调用点 annotation；
3. 函数 summary、递归 SCC、termination measure 与 checked lemma；
4. 参数化用户 ADT 的按使用点 monomorphisation；
5. functor/theory transformer 与 generativity。

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
