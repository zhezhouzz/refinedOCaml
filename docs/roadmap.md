# refinedOCaml roadmap

本文档记录 refinedOCaml 目前已经完成的内容、我们接下来计划实现的目标，以及相关论文阅读范围。

## 目标与进展

| 方向 | 目标 | 当前进展 | 状态 | 下一步 |
|---|---|---|---|---|
| A. 插入时机 | 在 OCaml normal typecheck 之后运行 refinement checker，并使用 Typedtree typing information | 已从 `.cmt/.cmti` 读取 Typedtree；PPX 只检查并保留 annotation；OCaml API 全部隔离在 `Ocaml_5_3_frontend` | 工程化完成 | 新 OCaml release 必须新增 versioned frontend 和 CI entry |
| A. 普通类型错误处理 | 只接受完整 typed implementation，拒绝 partial Typedtree | `obligations_of_cmt_with_theories` 只接受 `Implementation`，拒绝 `Partial_implementation` / `Partial_interface`；测试覆盖 ill-typed case | MVP 已完成 | 增加错误信息和 dune 集成 |
| B. Module theory | 用 module/signature 管理 predicates 和 axioms | 支持 predicate/axiom/lemma、abstract sorts、alias chain，以及具名 applicative/unit-generative functor theory；应用会克隆 result theory 并连接参数 theory | Functor MVP 已完成 | parameterized abstract sorts、nested/first-class functor 与 destructive substitution |
| B. Separate compilation | 防止 stale 或未导入的 refinement theory 被误用 | `.rmi` v5 保存 OCaml version、unit/digest、abstract sorts、aliases、functor templates 和 proof metadata | MVP 已完成 | 设计非 `Marshal` 的长期稳定格式 |
| B. Axioms vs lemmas | 区分 trusted assumptions 与 solver-checked theorem | `.mli` 支持 `refined.lemma`；导出前按顺序检查 VC；`.rmi` v3 保存 checked lemma、VC digest、solver identity/timeout 和依赖，客户端分别报告 provenance | MVP 已完成 | 可选 Z3 proof/外部 proof assistant certificate 与小型 replay kernel |
| B. ADT encoding | 将 OCaml ADT 编码成可查看的 SMT theory | 单态/参数化 ADT monomorphisation、dependency slicing 与 typed Logic AST expected-sort 消歧已完成；constructor/selector 在 SMT 前解析为具体实例 | Typed ADT MVP 已完成 | 研究更细的 constructor axiom bundle 与 abstract type theory |
| C. Safety vs coverage | 同时支持 over-approximate safety 和 under/coverage checking | Single-payload Return/Raised/Performed paths、state、CPS 与 effectful safety call summaries 已组合；caller handlers 可处理 callee outcomes | Payload outcome safety MVP 完成 | outcome coverage witnesses、recursive outcome summaries |
| C. 参数化 checker | 让 checker parameterized over denotation、typing algorithm、refinement domain | Hindley/Horn、summary、递归 SCC/measure 与 relational outcome algebra 位于稳定 Core | Safety/Generic/Coverage/Outcome core 完成 | outcome contracts 与 domain-specific state witnesses |
| C. Coverage typing algorithm | 支持 Coverage Type 风格的 under-approximate typechecking | 无 witness 保留 whole-image existential VC；完整 result-indexed witnesses 验证 constructive inverse，并在调用点 existentially 组合 call result/argument equations；递归使用 measure | Compositional MVP 已完成 | ghost state、nondeterministic relational witnesses 与 richer subtyping |
| 函数调用 | 支持 first-order 函数调用 | 本地 safety contract 可作为 summary；Tarjan SCC 识别直接/互递归；`int` parameter measure 对每条递归边生成非负和严格下降 VC | Safety MVP 已完成 | 支持结构 measure 与 compositional coverage summary |
| 多态 | 利用 Typedtree use-site type 做实例化 | predicate/axiom 及用户参数化 ADT 可按 obligation 实例化；普通多态函数 first-order inline 时替换整个 Core body | 部分完成 | 处理 polymorphic recursion 的拒绝/abstract theory 机制 |
| OCaml 语法覆盖 | 支持实用 OCaml 子集，并明确拒绝未建模特性 | 支持 single-payload raise/effect、payload binders、one-shot resume 与跨函数 safety outcome summaries | Payload outcome frontend MVP | outcome coverage、recursive summaries、multi-shot handlers |
| Solver 工程 | 生成 SMT-LIB，调用 Z3，输出 model | 已支持 `--emit-smt`、Z3 `sat/unsat/unknown`、model 输出 | MVP 已完成 | 记录 solver version、timeout、enabled axioms；改进 `unknown` 诊断 |
| 工程可复现性 | 让项目能在干净环境中稳定构建和测试 | 已有本机 OCaml 5.3.0 switch、direct-dependency lock、setup script、GitHub Actions、format gate、autofix.ci、deterministic property fuzzing 和版本升级规约 | 已完成 | CI 通过后保护主分支；新增 frontend 时扩展版本矩阵 |

## 阅读计划

| 论文 | 相关方向 | 为什么相关 | 阅读优先级 |
|---|---|---|---|
| `ranjit-2025-generic-refinement-types.pdf` | C | 已完成精读；提取 bidirectional judgment、subtyping constraints、Hindley evar 与 Horn generic 结构 | 已落实第一阶段 |
| `ranjit-2017-local-refinement-typing.pdf` | C | 适合研究局部化 refinement checking/inference，避免全局 constraint generation 过重 | 中 |
| `ranjit-2024-mechanizing-refinement-types.pdf` | B / TCB | 对 formalization 和可信 checker 很有启发，但当前阶段暂不实现 mechanization | 低，暂缓 |

暂时不读用户自己的 coverage paper；Ilya Sergey 近年 synthesis/separation-logic/verifier 论文也先不作为主线，除非项目后续转向 heap/effects、synthesis-guided witness、或 proof artifacts。

## 解释

### 1. 当前 MVP 已经解决了插入时机问题

项目最重要的工程选择是：refinement checker 不在 PPX expansion 阶段做语义检查，而是在 OCaml normal typecheck 完成之后读取 `.cmt/.cmti`。这样 refinement checker 可以依赖 OCaml 已经解析、消歧、实例化的 typing information。

这解决了我们最初担心的一个核心问题：PPX 只适合保留 annotation 和做轻量语法检查，不适合承担 refinement typing。当前设计方向是正确的。

### 2. Module theory 已有可工作的最小形态

现在 module/signature 可以导出 uninterpreted predicates 和 trusted axioms。`.rmi` 机制保证客户端只使用 interface 暴露的 theory，并通过 `.cmi` digest 避免 stale theory。

但这个机制目前还是一阶、非 functor、非 abstract-theory-transformer 的版本。它适合作为 MVP，但如果 OCaml module 真正成为 axiom/theory 管理层，后面必须处理 abstract types、functor generativity、module alias、checked lemmas 等问题。

### 3. 参数化 checker 是下一阶段的核心

当前代码已经完成工程层拆分，并加入由 refinement domain 与 denotation 参数化的 compositional
checking/synthesis/subtyping skeleton。Safety/Coverage 的生产 VC 已通过这一 skeleton 生成；完整设计与
论文映射记录在 `docs/generic-refinement-design.md`。

| 层 | 职责 |
|---|---|
| Versioned frontend | OCaml Typedtree 到 refined Core 的翻译，随 OCaml 版本变化 |
| Stable Core | 与 OCaml 版本无关的表达式、类型、pattern、module theory IR |
| Denotation interface | 不同 refinement/coverage/safety 语义对 Core 的解释 |
| Typing algorithm | 语法导向的 checking/inference/subtyping 规则 |
| VC backend | SMT obligation、solver 调用、model 解释、proof artifact |

论文实际重点是 generic refinement parameters，而不是直接统一 Safety/Coverage。我们采用其
bidirectional/subtyping/evar 结构，同时保留 Safety 与 Coverage 的 denotation 差异。higher-sorted
Hindley schemes 已完成 `.mli/.rmi` surface 与 resolved-call integration；非递归正向 Horn
constraint generation/solving 也已接入同一条生产路径。

### 4. Coverage 目前只是 VC，不是真正的 coverage type system

无 witness coverage 的含义仍是整函数 image 的 under-approximation obligation：

```text
forall result. post(result) => exists input. pre(input) /\ result = f(input)
```

完整 witnesses 会把 existential 输入替换为 result-indexed inverse，并形成可组合 call judgment。后续仍需决定：

- coverage judgment 是否和 safety 共享同一 Core typing skeleton；
- ghost state 与 nondeterministic witness relations 如何表达；
- coverage subtyping/entailment 是否能复用 safety 的 refinement domain；
- nondeterminism、effects、exceptions 是否需要 relational outcome semantics。

### 5. 工程可复现基线已经建立

仓库现在固定 OCaml 5.3.0，提交 `refined_ocaml.opam.locked`，提供 `dev/setup-switch.sh`，并由 GitHub
Actions 运行 `@all/@install/@refined/@fmt/@fuzz`，autofix.ci 自动提交 `dune fmt` 修复。fuzz job 固定
seed 跑 20,000 个 evar/Hindley/Horn/function-SCC/theory-slice cases，并用图闭包作 oracle。`refined_ocaml.ir`
不依赖 compiler-libs；所有版本敏感 API 集中在 `Ocaml_5_3_frontend`。升级流程记录在
`docs/versioning.md`。

Generic Refinement Types 的 Hindley/Horn surface、result propagation 与 mutually-recursive symbolic
CHC fixpoint 已经落实。函数 safety summary、递归 call-graph SCC 与路径敏感的 termination measure
也已经接入生产 VC 路径；summary 会由各函数自己的 obligation 检查，不进入 trusted axiom 集合。

Checked lemma 与 verification-artifact 导出也已经落实：失败或 unknown 的 lemma 不会进入 `.rmi`，
checked lemma 不计入 trusted axiom provenance。当前 artifact 记录 VC digest、solver identity 和 timeout，
但还不是可由小型 kernel 独立重放的 proof certificate。

参数化用户 ADT 的 use-site monomorphisation 也已完成。每个 obligation 只实例化实际出现的闭合
sort；constructor family 按 result sort 隔离；多态 first-order inline 会同步替换 body/pattern/field
sort。开放实例无法有限化时 fail closed。

Dependency-driven ADT/axiom slicing 也已完成。Contract/Core/summary symbols 构成 roots，axiom 与
lemma symbols 及 verification-artifact dependencies 构成保守 least closure；logic declarations、
provenance、artifacts 与 ADT bundle 一起过滤。只作为值流过的 ADT 保持 opaque sort。

带 expected sort 的 typed Logic AST 也已完成。Equality 双向传播 sort，constructor 使用 expected
result/argument sorts，field 使用 receiver sort；SMT translation 与 slicing 共享同一个 resolved AST，
不再各自猜测短名。

Module alias 与单态 abstract type theory 也已完成。Signature/local aliases 作为 longest-prefix path
rewrite 链式展开；abstract sort 按 lexical scope 解析，并与客户端 Typedtree sort identity 对齐；`.rmi`
格式随后随 functor template 升级到 v5。

Functor theory transformer 与 generativity MVP 也已完成。具名参数应用使用 `F(Arg)` applicative sort
identity，unit functor application 使用目标 module path 生成 fresh identity；result predicates/axioms 和
parameter aliases 会在 application 处实例化。

Compositional coverage judgment 与 witness-carrying under-summary 也已完成。完整 witness mapping 会把
whole-image existential 加强为可检查的 inverse，并在调用点通过 existential call result、callee post 和
argument/witness equations 组合；递归调用继续受 measure 约束。

Relational outcome/state semantics 已完成为稳定 Core algebra：guarded paths 携带 initial/final state 与
Return/Raised/Performed outcomes；bind、branch、state update、exception/effect handler，以及 relational
Safety/Coverage VC templates 均有单元测试和 property fuzz。

Nullary `raise`/`try` lowering 与 outcome contract surface 已接入生产 backend。`raises = [(E,p)]` 为
Raised paths 提供 exceptional post；未列出异常失败；精确 handler/catch-all 会关系化处理 paths。

Local references/assignment lowering 与 state contracts 已完成。Lexical cells 映射到 relational ghost
state，branch/sequence/raise/handler 都显式 thread final state；normal post 可用 `state=[(cell,p)]` 检查
每条 path。Reference 参数、alias 和 escape 保持 fail closed。

Nullary `Effect.perform`、canonical abortive `Effect.Deep.match_with` 和 `performs` outcome contracts 已接入
生产 backend。Performed paths 可被 handler 消除或由 contract 检查，local state 会传入 handler。

Resumptive effect continuation semantics 已完成。CPS translator 为 Perform path 保存 continuation，
`continue k value` 恢复剩余 computation；deep handler 会处理 resumed continuation 的后续 perform，并
保留 relational state。当前仅支持 canonical one-shot resume。

Single-payload exception/effect 与 effectful safety call summaries 已完成。Payload 有独立 sort 和 symbolic
term；caller summary 同时生成 normal/Raised/Performed paths，callee precondition 单独检查，Performed
path 捕获 caller continuation。Cross-function state 和 recursive outcome summaries 保持 fail closed。

roadmap 的下一实现步骤是 exception/effect coverage outcome witnesses，然后加入 recursive effectful
summary 的 measure rule。
