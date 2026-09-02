# refinedOCaml roadmap

本文档记录 refinedOCaml 目前已经完成的内容、我们接下来计划实现的目标，以及相关论文阅读范围。

## 目标与进展

| 方向 | 目标 | 当前进展 | 状态 | 下一步 |
|---|---|---|---|---|
| A. 插入时机 | 在 OCaml normal typecheck 之后运行 refinement checker，并使用 Typedtree typing information | 已从 `.cmt/.cmti` 读取 Typedtree；PPX 只检查并保留 annotation；OCaml API 全部隔离在 `Ocaml_5_5_frontend` | 工程化完成 | 新 OCaml release 必须新增 versioned frontend 和 CI entry |
| A. 普通类型错误处理 | 只接受完整 typed implementation，拒绝 partial Typedtree | `obligations_of_cmt_with_theories` 只接受 `Implementation`，拒绝 `Partial_implementation` / `Partial_interface`；测试覆盖 ill-typed case | MVP 已完成 | 增加错误信息和 dune 集成 |
| B. Module theory | 用 module/signature 管理 predicates 和 axioms | 支持 predicate/axiom/lemma、abstract sorts、alias chain，以及具名 applicative/unit-generative functor theory；应用会克隆 result theory 并连接参数 theory | Functor MVP 已完成 | parameterized abstract sorts、nested/first-class functor 与 destructive substitution |
| B. Separate compilation | 防止 stale 或未导入的 refinement theory 被误用 | `.rmi` v8 为 OCaml cache；稳定 RPA1 sidecar 保存 unit/interface/proof records 并强制匹配 | Stable proof sidecar 完成 | theory cache 的非 Marshal 长期格式 |
| B. Axioms vs lemmas | 区分 trusted assumptions 与 solver-checked theorem | Artifact 保存 statement/VC SHA-256、完整 SMT、solver/timeout/依赖；小型 kernel 校验并重解 | Replay MVP 已完成 | 原生 Z3/外部 assistant certificate kernel |
| B. ADT encoding | 将 OCaml ADT 编码成可查看的 SMT theory | 单态/参数化 ADT monomorphisation、dependency slicing 与 typed Logic AST expected-sort 消歧已完成；constructor/selector 在 SMT 前解析为具体实例 | Typed ADT MVP 已完成 | 研究更细的 constructor axiom bundle 与 abstract type theory |
| C. Safety vs coverage | 同时支持 over-approximate safety 和 under/coverage checking | First-class identity、named deep regions、affine consume、borrow/transfer、frame 与 relational ghosts 已组合 | Region-typed relational heap/outcome MVP 完成 | ownership polymorphism 与 region inference |
| C. 参数化 checker | 让 checker parameterized over denotation、typing algorithm、refinement domain | Hindley/Horn、递归 measure、relational outcomes/witnesses、typed ADT ghosts 与 frame rules 位于稳定 Core | Safety/Generic/Coverage/Outcome core 完成 | observable identity 与 separation-style ownership domain |
| C. Coverage typing algorithm | 支持 Coverage Type 风格的 under-approximate typechecking | Functional/relational inverses、closed typed ghosts、normal/abnormal footprint targets；relation 检查 totality/soundness | Framed relational coverage MVP 已完成 | escaping references 与 ownership-aware witnesses |
| 函数调用 | 支持 first-order 函数调用 | 本地 safety contract 可作为 summary；Tarjan SCC 识别直接/互递归；`int` parameter measure 对每条递归边生成非负和严格下降 VC | Safety MVP 已完成 | 支持结构 measure 与 compositional coverage summary |
| 多态 | 利用 Typedtree use-site type 做实例化 | predicate/axiom 及用户参数化 ADT 可按 obligation 实例化；普通多态函数 first-order inline 时替换整个 Core body | 部分完成 | 处理 polymorphic recursion 的拒绝/abstract theory 机制 |
| OCaml 语法覆盖 | 支持实用 OCaml 子集，并明确拒绝未建模特性 | 支持 first-class `ref`、named recursive regions、borrow/transfer、affine consume、relational `match` | Region ownership + linear continuation MVP | region polymorphism/inference；显式 clone API 后再做 multi-shot |
| Solver 工程 | 生成 SMT-LIB，调用 Z3，输出 model | 已支持 `--emit-smt`、Z3 `sat/unsat/unknown`、model 输出 | MVP 已完成 | 记录 solver version、timeout、enabled axioms；改进 `unknown` 诊断 |
| 工程可复现性 | 让项目能在干净环境中稳定构建和测试 | 已有本机 OCaml 5.5.0 switch、direct-dependency lock、setup script、GitHub Actions、format gate、autofix.ci、deterministic property fuzzing 和版本升级规约 | 已完成 | CI 通过后保护主分支；新增 frontend 时扩展版本矩阵 |

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

完整 functional witnesses 或 `witness_relation` 会形成可组合 call judgment。Relational summary 同时生成
target-totality 和 pointwise-soundness obligations，避免把“存在某个相关输入”错误地当成“所有相关输入都
可用”。后续仍需决定：

- coverage judgment 是否和 safety 共享同一 Core typing skeleton；
- first-class identity、escaping references 与 ownership 如何表达；
- coverage subtyping/entailment 是否能复用 safety 的 refinement domain；
- nondeterminism、effects、exceptions 是否需要 relational outcome semantics。

### 5. 工程可复现基线已经建立

仓库现在固定 OCaml 5.5.0，提交 `refined_ocaml.opam.locked`，提供 `dev/setup-switch.sh`，并由 GitHub
Actions 运行 `@all/@install/@refined/@fmt/@fuzz`，autofix.ci 自动提交 `dune fmt` 修复。测试由 Alcotest
分组；fuzz job 用 QCheck2 固定 seed 跑 20,000 个 evar/Hindley/Horn/function-SCC/theory-slice cases，失败时
缩减 case seed，并用图闭包作 oracle。CLI 使用 Cmdliner 子命令。`refined_ocaml.ir`
不依赖 compiler-libs；所有版本敏感 API 集中在 `Ocaml_5_5_frontend`。升级流程记录在
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

Compositional coverage judgment 与 witness-carrying under-summary 也已完成。完整 functional mapping 或
relational witness 会把 whole-image existential 加强为可检查的 inverse；调用点 existentially 选择 call
result/ghost，再加入 witness equations 或 relation。递归调用继续受 measure 约束。

Relational outcome/state semantics 已完成为稳定 Core algebra：guarded paths 携带 initial/final state 与
Return/Raised/Performed outcomes；bind、branch、state update、exception/effect handler，以及 relational
Safety/Coverage VC templates 均有单元测试和 property fuzz。

Nullary `raise`/`try` lowering 与 outcome contract surface 已接入生产 backend。`raises = [(E,p)]` 为
Raised paths 提供 exceptional post；未列出异常失败；精确 handler/catch-all 会关系化处理 paths。

Local references/assignment lowering 与 state contracts 已完成。每种 content sort 使用 SMT array heap，
reference value 是独立 identity；`!r`/`r := v` 分别编码为 `select`/`store`。动态 `ref` 分配 fresh identity，
lexical aliases 保留同一 identity，branch/sequence/raise/handler 都显式 thread final heap。

Nullary `Effect.perform`、canonical abortive `Effect.Deep.match_with` 和 `performs` outcome contracts 已接入
生产 backend。Performed paths 可被 handler 消除或由 contract 检查，local state 会传入 handler。

Resumptive effect continuation semantics 已完成。CPS translator 为 Perform path 保存 continuation，
`continue k value` 恢复剩余 computation；deep handler 会处理 resumed continuation 的后续 perform，并
保留 relational state。当前仅支持 canonical one-shot resume。

Single-payload exception/effect 与 effectful safety call summaries 已完成。Payload 有独立 sort 和 symbolic
term；caller summary 同时生成 normal/Raised/Performed paths，callee precondition 单独检查，Performed
path 捕获 caller continuation。`outcome_state` 可分别描述 Raised/Performed 的 final heap，并在 caller
捕获或处理 outcome 前完成 heap update。

Exception/effect coverage outcome witnesses 已完成。`outcomes=(kind,name,post,witnesses)` 分别生成
payload target reachability VC；under callers 可组合 callee normal/Raised/Performed constructive paths，
Performed paths 携带 caller continuation。

Measured recursive outcome summaries 已完成。Relational CPS thread source path conditions；Safety 的 callee
pre/measure 成为 guarded side obligations，Coverage 的 measure 成为 constructive reachability guard；缺失
measure 会拒绝。

State/heap coverage witnesses 与跨函数 state summaries 已升级为 alias-aware heap model。
`requires_state`通过 initial heap `select` 约束输入，`state`描述 final targets，`state_witnesses`构造 coverage
initial heap；safety/coverage calls 以 `store` 更新 caller heap。同一 actual identity 对应的多个 summary
输出会生成一致性约束，动态分配同时生成 freshness 约束。

Conditional-linear continuation contracts 已完成。Handler action 可递归表示 guarded Abort/Resume；payload
和 outer state 可参与条件。Non-tail 或同一路径多次 resume 会拒绝，因为 OCaml Deep continuation 是
one-shot，不能伪装成 multi-shot。

Stateful nondeterminism 已完成。Frontend 不再把 `choose` alternatives 预先 ANF 成顺序求值；relational
backend 将两个 computation 保留为 path union，因此 Safety 对所有分支检查，Coverage 只需为目标找到
至少一条分支。分支可独立写 heap、raise 或 perform。

Relational witnesses 与 ghost-state synthesis 已完成。`witness_relation` 可同时引用普通参数、目标、
`old_<ref>` initial heap contents 和 typed existential ghosts；normal 与 Raised/Performed summaries
都能跨函数组合。Functional witnesses 保持兼容，但不能与 relation 混用。

Typed ADT ghosts 与 heap footprint/frame clauses 已完成。Ghost sort 使用 OCaml core-type syntax，支持
primitive、tuple、list/option、闭合用户 ADT 与 abstract sort，并进入 use-site monomorphisation。
`modifies`/`outcome_modifies` 声明 reference-parameter footprint；未修改 cell 生成 alias-aware frame，
Safety 可 havoc 无 predicate 的 modified cell，Coverage 则要求每个 modified cell 有 final target。Translator
同时统一恢复函数 entry heap，避免 literal assignment 把 parameter `old`/frame 错写成中间 heap；局部
reference 则单独保存 allocation-time initial value。

First-class reference identity、pointer equality 与 direct escaping discipline 已完成。`ref init` 可作为普通
Core expression；`==/!=` 只接受相同 content sort 的 refs。Ref-returning contracts 必须以 `result_state`
描述 final content，并可用 `result_fresh` 声明新 identity；Safety/Coverage summaries 都会把 returned content
写入 caller heap，fresh results 会加入后续 allocation 的 distinct 集合。

Reference-containing tuple/ADT ownership 与 reachable-heap contracts 已完成于 finite non-recursive shape。
`result_references` 使用 tuple index/`Constructor.index` path 精确覆盖所有 returned ref fields；variant path
由 recognizer guard，summary 以 guarded store 转移 content。`result_fresh_references` 同时检查 entry
separation 和 returned paths 间的 pairwise separation。Relational `Match` 也已支持在 pattern branch 中继续
deref/effectful computation。递归 reachable shape 会拒绝而非静默截断。

Recursive ownership frontier 与 borrow/transfer permissions 已完成。`result_recursive = true` 把 recursive
shape 的 path 解释为逐 summary 边界重检的 constructor frontier，而不是一次性深层 invariant；未显式开启
仍 fail closed。`result_reference_permissions` 的 borrow 必须 alias entry ref，并继承 frame；transfer 要求
fresh separation 并转移 content。Predicate 可引用 path `identity`，所以 alias relation 也能模块化检查。

Deep recursive region invariants 与 affine ownership consumption 已完成。`result_region` 命名兼容的
recursive frontier spec；producer 的 recursive fields 必须由同 region provenance 归纳构造。
`requires_regions` 在 entry VC 展开当前 frontier，并作为跨 summary 边界重新获得 invariant 的 token；
`consumes_regions` 通过 origin tracking 拒绝 double consume、use-after-consume 和 borrowed-alias consume。
Pattern match 消费旧 root，并为 recursive subfields 创建新 region origins。

稳定 proof artifact 格式与小型 replay kernel 已完成。RPA1 是版本化 netstring sidecar，绑定 canonical
lemma statement、完整 SMT VC、两类 SHA-256、solver/timeout 和 checked dependency order。Replay 先做有界
parse、digest/拓扑校验，再以当前 Z3 重解全部 VC。`.rmi` 升到 v8，import 必须携带内容完全一致的 sidecar；
Marshal 只作为 OCaml-specific theory cache。RPA1 是 replay record，而非原生 solver proof certificate。

roadmap 的下一实现步骤是基于 VC/theory digest 的增量验证缓存。
