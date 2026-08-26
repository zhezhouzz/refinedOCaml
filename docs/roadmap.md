# refinedOCaml roadmap

本文档记录 refinedOCaml 目前已经完成的内容、我们接下来计划实现的目标，以及相关论文阅读范围。

## 目标与进展

| 方向 | 目标 | 当前进展 | 状态 | 下一步 |
|---|---|---|---|---|
| A. 插入时机 | 在 OCaml normal typecheck 之后运行 refinement checker，并使用 Typedtree typing information | 已从 `.cmt/.cmti` 读取 Typedtree；PPX 只检查并保留 annotation；OCaml API 全部隔离在 `Ocaml_5_3_frontend` | 工程化完成 | 新 OCaml release 必须新增 versioned frontend 和 CI entry |
| A. 普通类型错误处理 | 只接受完整 typed implementation，拒绝 partial Typedtree | `obligations_of_cmt_with_theories` 只接受 `Implementation`，拒绝 `Partial_implementation` / `Partial_interface`；测试覆盖 ill-typed case | MVP 已完成 | 增加错误信息和 dune 集成 |
| B. Module theory | 用 module/signature 管理 predicates 和 axioms | `.mli` 可导出 `[@@refined.predicate]` 和 `[@@@refined.axiom]`；`.cmti -> .rmi`；客户端通过 `--theory` 导入 | MVP 已完成 | 支持 abstract type theory、module alias、functor theory transformer |
| B. Separate compilation | 防止 stale 或未导入的 refinement theory 被误用 | `.rmi` 保存 OCaml version、unit name、`.cmi` digest；加载时检查 imports 和 digest | MVP 已完成 | 设计 `.rmi` 稳定格式，避免直接 `Marshal` 作为长期 artifact |
| B. Axioms vs lemmas | 当前允许 trusted axioms；未来希望支持 checked lemmas | 当前 axiom 全部进入 TCB，并在结果中列出 trusted axiom 名称 | 部分完成 | 加入 `lemma` 语法、lemma VC、导出已检查 lemma |
| B. ADT encoding | 将 OCaml ADT 编码成可查看的 SMT theory | 单态 variant/record 已支持；constructor、recognizer、selector 和基本代数 axioms 已生成 | MVP 已完成 | 支持参数化用户 ADT 的 use-site monomorphisation；加入 axiom slicing |
| C. Safety vs coverage | 同时支持 over-approximate safety 和 under/coverage checking | `Vc_semantics.Safety` 与 `Vc_semantics.Coverage` 实现两套纯 VC template；同一 binding 可同时声明 over 和 coverage | MVP 已完成 | 从 whole-function VC 过渡到真正可组合的 typing judgment |
| C. 参数化 checker | 让 checker parameterized over denotation、typing algorithm、refinement domain | `Refinement_domain.S`、`Typing_judgment.Make` 和 `Evar_context.Make` 已进入 compiler-independent IR；生产 VC 通过 compositional Safety/Coverage subsumption；use-site specialization 使用通用 evar unifier | compositional skeleton 完成 | 增加 higher-sorted Hindley scheme/application elaboration，再实现 Horn constraints |
| C. Coverage typing algorithm | 支持 Coverage Type 风格的 under-approximate typechecking | 当前 coverage 是 `forall result. post(result) => exists input. pre(input) /\ result = f(input)` 的 SMT obligation | 未完成 | 设计 coverage judgment、subtyping/entailment、witness/inverse 支持 |
| 函数调用 | 支持 first-order 函数调用 | 当前通过 inlining 处理本文件中的 first-order 函数；递归调用被拒绝 | 部分完成 | 加入函数 summary、递归 SCC、termination measure |
| 多态 | 利用 Typedtree use-site type 做实例化 | predicate/axiom 的 type variable 可按 obligation 实例化；普通多态函数可 first-order inlining | 部分完成 | 用户参数化 ADT 的 monomorphisation；处理 polymorphic recursion 的拒绝/抽象机制 |
| OCaml 语法覆盖 | 支持实用 OCaml 子集，并明确拒绝未建模特性 | 支持 int/bool、算术、if、简单 let、tuple、单态 ADT/record、exhaustive match；拒绝高阶、递归、mutation、exception、effect 等 | MVP 已完成 | 按优先级扩展 match/records/modules，再考虑 effectful core |
| Solver 工程 | 生成 SMT-LIB，调用 Z3，输出 model | 已支持 `--emit-smt`、Z3 `sat/unsat/unknown`、model 输出 | MVP 已完成 | 记录 solver version、timeout、enabled axioms；改进 `unknown` 诊断 |
| 工程可复现性 | 让项目能在干净环境中稳定构建和测试 | 已有本机 OCaml 5.3.0 switch、direct-dependency lock、setup script、GitHub Actions、format gate、autofix.ci 和版本升级规约 | 已完成 | CI 通过后保护主分支；新增 frontend 时扩展版本矩阵 |

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
bidirectional/subtyping/evar 结构，同时保留 Safety 与 Coverage 的 denotation 差异。下一 slice 是
higher-sorted Hindley schemes 和 application elaboration；Horn solving 后置。

### 4. Coverage 目前只是 VC，不是真正的 coverage type system

当前 coverage 的含义是整函数 image 的 under-approximation obligation：

```text
forall result. post(result) => exists input. pre(input) /\ result = f(input)
```

这可以验证一些简单函数和 finite choice，但它还不是可组合的 coverage typing algorithm。未来需要决定：

- coverage judgment 是否和 safety 共享同一 Core typing skeleton；
- under 的 witness/inverse 信息如何表达；
- coverage subtyping/entailment 是否能复用 safety 的 refinement domain；
- nondeterminism、effects、exceptions 是否需要 relational outcome semantics。

### 5. 工程可复现基线已经建立

仓库现在固定 OCaml 5.3.0，提交 `refined_ocaml.opam.locked`，提供 `dev/setup-switch.sh`，并由 GitHub
Actions 运行 `@all/@install/@refined/@fmt`，autofix.ci 自动提交 `dune fmt` 修复。`refined_ocaml.ir` 不依赖 compiler-libs；所有版本敏感 API
集中在 `Ocaml_5_3_frontend`。升级流程记录在 `docs/versioning.md`。

Generic Refinement Types 的第一阶段已经落实。roadmap 的下一实现步骤切换为 higher-sorted Hindley
generic scheme/application elaboration，并要求在调用结束时 evar context 完整；之后才加入 Horn solver。
