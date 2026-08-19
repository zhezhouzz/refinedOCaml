# refinedOCaml

`refinedOCaml` 是一个把双向 refinement types 植入 OCaml 的研究原型。它同时表达：

- **over-approximation**：所有实际结果都满足后置条件，用来证明 safety/correctness；
- **under-approximation**：后置条件描述的每个结果都确实可达，用来证明 reachability/incorrectness。

它不会把用户 datatype 偷换成求解器内建 datatype。每个 OCaml ADT 默认编码为一个
**uninterpreted sort**，构造器、recognizer 和 selector 都是 uninterpreted symbols，代数性质由
生成的显式 axioms 给出。

## 当前可运行的原型

```ocaml
let[@refined.over { pre = "x >= 0"; post = "result > x" }]
    succ (x : int) : int =
  x + 1

let[@refined.under { pre = "x >= 0"; post = "result >= 1" }]
    positive_range (x : int) : int =
  x + 1
```

验证：

```sh
dune build
dune exec refined-ocaml -- examples/valid.ml
dune exec refined-ocaml -- --emit-smt work/smt examples/valid.ml
dune runtest
```

PPX `refined_ocaml.ppx` 检查属性形状，并在真正编译 OCaml 时去掉验证专用属性：

```lisp
(preprocess (pps refined_ocaml.ppx))
```

验证器仍应独立地在原始 `.ml` 文件上运行；PPX 不是可信验证核心，也不在编译过程中偷偷写
sidecar 文件。

## 两种 refinement 的精确定义

对纯函数 `f : X -> Y`：

```text
over  {P} f {Q}    ≜    ∀x. P(x) ⇒ Q(x, f(x))
under [P] f [Q]    ≜    ∀y. Q(y) ⇒ ∃x. P(x) ∧ y = f(x)
```

因此 under 合约描述的是函数 image 的一个下界。它不是把普通 Hoare triple 的蕴含方向机械
反转。当前 under 的 `post` 只应引用 `result`；后续版本会加入显式 ghost variables，以表达输入/
输出状态之间的可达关系。

验证器把 over 的反例和 under 的“缺失结果”分别交给 Z3：两者都是查找否定公式是否
`unsat`。`sat` 时输出模型。

## ADT 编码

例如：

```ocaml
type nat = Z | S of nat
```

会产生形如下面的 SMT 签名：

```smt2
(declare-sort T_nat 0)
(declare-fun C_nat_Z () T_nat)
(declare-fun C_nat_S (T_nat) T_nat)
(declare-fun is_C_nat_Z (T_nat) Bool)
(declare-fun is_C_nat_S (T_nat) Bool)
(declare-fun sel_C_nat_S_0 (T_nat) T_nat)
```

以及显式 axioms：

- 构造结果满足相应 recognizer；
- 不同构造器互斥；
- selector 在对应构造结果上返回参数；
- recognizer 蕴含用 selectors 重建原值；
- 每个 carrier 元素至少属于一个构造器。

这些 axioms 给出 disjointness、injectivity、exhaustiveness，但**默认没有 induction axiom**。
因此模型仍可包含非标准或循环元素。需要归纳证明时，计划通过 well-founded measure、用户 lemma
或有限展开显式加入；不会假装一阶 axioms 已经完整刻画 least fixed point。

## 当前支持范围

第一版刻意是 first-order、pure、monomorphic 的闭环：

| 特性 | 状态 | 编码 |
|---|---:|---|
| `int` / `bool`、算术、比较、布尔连接 | 支持 | SMT Int/Bool |
| `if`、局部简单 `let` | 支持 | `ite` / substitution |
| 单态 variant、构造器、`match` | 支持 | uninterpreted sort + axioms |
| 单态 immutable record、读取字段 | 支持 | 单构造器 + selectors |
| over / under 合约 | 支持 | validity / image coverage |
| 反例模型、导出 SMT-LIB | 支持 | Z3 model / `--emit-smt` |
| 多态 ADT、高阶函数、递归、跨函数调用 | 明确拒绝 | 下一阶段需要 monomorphisation / summaries |
| mutable state、exception、algebraic effects | 明确拒绝 | relational state transition theory |
| GADT、first-class module、object | 明确拒绝 | typed frontend + feature-specific theory |

未支持的构造会报错，不会被当成 unconstrained term 后继续“证明”。

## 完整语言路线

详细设计见 [`docs/design.md`](docs/design.md)。推荐的实施顺序是：

1. 接入 Typedtree，消除当前依赖显式参数/返回类型以及默认 `int` 的限制；
2. 加入函数 summary、SCC 递归验证、termination/measure 和 lemma；
3. 对参数化类型做按使用点 monomorphisation，仍保持 uninterpreted-sort 编码；
4. 用关系语义统一 mutation、exception、effect handler 与 under-approximation；
5. 加入 module signature 中的 refinement、抽象类型封装和 separate compilation；
6. 最后处理 GADT equality witnesses、polymorphic variants、objects 和并发内存模型。

`src/refined_core.ml` 目前是可替换的小型可信核心；PPX、Typedtree 前端和模型展示都不应成为
soundness 的隐式依赖。

