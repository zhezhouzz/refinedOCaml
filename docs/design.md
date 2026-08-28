# refinedOCaml design note

## 1. 设计原则

1. OCaml 类型检查器仍负责普通类型安全；refinedOCaml 只在 Typedtree 之后增加逻辑义务。
2. over 与 under 是两种不同的 judgment，共享表达式语义但不共享错误的蕴含模板。
3. 用户 datatype 的 SMT 表示必须可查看、可替换；默认是 uninterpreted sorts + named axioms。
4. 遇到无法建模的 OCaml 特性时拒绝验证。禁止用 fresh unconstrained value 掩盖语义缺失。
5. trusted computing base 最终只包含 Typedtree-to-core 翻译、VC 生成和 SMT proof checking。

## 2. 核心 judgment

无 effect 的表达式翻译为关系 `Eval(e, σ, r, σ')`。纯函数只是它的特例：

```text
Over(P, e, Q)  = ∀σ r σ'. P(σ) ∧ Eval(e,σ,r,σ') ⇒ Q(σ,r,σ')
Under(P, e, Q) = ∀σ' r. Q(σ',r) ⇒ ∃σ. P(σ) ∧ Eval(e,σ,r,σ')
```

这一定义让 mutation、exception 和 algebraic effects 能在以后自然接入，而不必重新定义 under。
非终止可作为独立 outcome；是否要求 total correctness 由合约模式决定。

建议最终提供四个 mode：

```text
over-partial   over-total   under-may   under-must
```

当前 MVP 实现 `over-partial` 的一阶片段；递归 safety 通过 independently checked summary 和
well-founded `int` measure 处理。确定性或有限 `choose` 纯函数支持 whole-image `under-may`；完整的
result-indexed inverse witnesses 可形成 compositional under-summary，并在 measure 下支持递归。

## 3. 合约表面语法

当前属性语法可直接被 OCaml parser 接受：

```ocaml
let[@refined.over  { pre = "..."; post = "..." }] f ... = ...
let[@refined.coverage { pre = "..."; post = "..." }] g ... = ...
```

已支持的递归语法：

```ocaml
let[@refined.over { pre = "n >= 0"; post = "..." }]
   [@refined.measure "n"] rec fold n = ...
```

后续兼容语法：

```ocaml
type pos = int [@@refined "v > 0"]
val f : (x : int) -> int
  [@@refined.over  "x >= 0 ==> result > x"]
  [@@refined.under "result > 0"]

axiom[@refined.axiom] name = "forall ..."
```

字符串中的逻辑先复用 OCaml expression parser，随后 elaboration 到与 compiler-libs 隔离、每个节点
带 sort 的 Logic AST。当前支持 expected-sort constructor/field 消歧；后续仍需独立 surface parser、
quantifier、set、map、bitvector、浮点语义与 ghost binders。

## 4. Datatype theory

对每个实例化后的类型 `T` 声明 sort。每个 constructor `C : A1 * ... * An -> T` 声明：

```text
C      : A1 × ... × An → T
is_C   : T → Bool
sel_Ci : T → Ai
```

默认 axiom bundle：constructor recognition、cross-constructor exclusion、selector reduction、
recognizer completeness、constructor coverage。可以按验证目标启用更弱的 bundle，以减少 quantifier。

不默认声称这些有限一阶 axioms 给出了 initial algebra。可选 induction 支持：

- structural measure 映射到 Int，并加入严格下降义务；
- 对当前 conjecture 生成局部 induction lemma；
- bounded unfolding，用于 under 的具体 witness 搜索；
- 外部 proof assistant 证明的 lemma 作为已签名 artifact 导入。

参数化 ADT 不使用一个魔法 polymorphic SMT sort。按调用图和规范中的具体 type application
monomorphise；真正无法有限实例化的 polymorphic recursion 需要显式 abstract theory。

## 5. OCaml 特性

### Modules 与抽象类型

MVP 将 `.mli` 中公开的 predicates/axioms 编译成带 `.cmi` digest 的 `.rmi`；客户端不会看到实现侧
private axioms。单态抽象类型已导出为 scoped uninterpreted sort，applicative module aliases 已作为路径
重写处理。一阶具名参数 functor 和 unit-generative functor 已可变换 theory；parameterized abstract
sorts、nested/first-class functor、destructive substitution 和 abstract measure 仍是后续工作。

### Mutation

heap 使用 typed regions 或 separation-style chunks，不把整个 OCaml heap 粗暴编码成单一数组。
over 跟踪所有可能后状态；under 必须生成能到达目标 heap 的前状态/witness。

### Exceptions

结果 sort 是 `Normal v | Raised exn` 的关系化 outcome。合约分别写 `ensures` 与 `raises`；异常不会
被当成任意值，也不会让 postcondition vacuous。

### Algebraic effects

表达式语义产生 free-monad 风格的 effect tree，handler 是 tree transformer。第一阶段只支持封闭
effect rows；开放 effect 与 continuation 多次恢复需要线性/重复使用信息。

### GADT

Typedtree 提供 constructor 引入的局部类型等式。将等式作为 branch-local evidence，而不是全局
datatype axiom。existential type arguments skolemise，离开 branch 时不能逃逸。

### Higher-order functions

函数值使用 apply relation 和 contract closure；常用直接调用保持 first-order defunctionalisation。
under 合约需要可构造的 closure witness，不能只靠 over-style universal summary。

### Objects、polymorphic variants、lazy、并发

- object row 编码为 method dictionary theory；self type 需要递归 sort；
- polymorphic variant 使用 row-aware tags，开放 row 不加 exhaustiveness；
- `lazy` 显式建模 unevaluated/value/exception 三态和 memoisation；
- 并发必须选择内存模型后再实现，绝不默认顺序一致性冒充 OCaml runtime 语义。

## 6. 求解与可信度

量词 axioms 很容易使 SMT 不稳定。工程实现应包含：

- axiom slicing：只实例化当前 VC 可达的 sorts/constructors；
- triggers 可查看并允许覆写；
- under 优先支持用户 witness/inverse，将 `∀∃` VC Skolem 化为可检查的量词较少义务；
- 每个结果保存 SMT-LIB、solver version、timeout 和 enabled axiom bundle；
- `unknown` 永远不是成功；
- 可选 proof-producing backend 或把关键 lemma 导出到 Lean/Coq。

## 7. 分阶段里程碑

### MVP（本仓库）

保留 PPX 属性的 Typedtree frontend、typed Core、纯一阶算术、tuple、单态 ADT/record、
first-order inlining、module-scoped theory、`.cmti/.rmi` separate compilation、over/coverage VC、
有限 choice、safety function summary、递归 SCC/measure、Z3、模型与 SMT 导出。

### M1

state/heap coverage summaries、可重放 proof certificate、增量缓存。

### M2

关系化 core IR、references/arrays/exceptions、ghost state、under witness syntax、路径级 counterexample。

### M3

functor/theory transformers、GADT、polymorphic variants、higher-order contracts、algebraic effect handlers。

### M4

proof artifacts、IDE/LSP、dune rule、并发语义、标准库 refinement signatures。
