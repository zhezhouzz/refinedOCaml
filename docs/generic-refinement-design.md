# Generic refinement typing design

This note records the design extracted from *Generic Refinement Types* (Lehmann et al., POPL 2025) and how
it maps to refinedOCaml. It is intentionally narrower than implementing all of Flux.

## What the paper contributes

The paper does not present a generic Safety/Coverage verifier. Its reusable contribution is an algorithmic
refinement-typing structure with:

- bidirectional checking and synthesis judgments;
- syntax-directed subtyping that emits constraints;
- Hindley (`hdl`) generic refinements instantiated by evars and syntactic unification at call sites;
- Horn (`hrn`) generic refinements instantiated by Horn variables and constraint solving;
- well-formedness conditions that keep generated queries first-order and SMT-decidable.

The four important well-formedness invariants are:

1. Horn generics occur only positively, outside negation and disjunction;
2. higher-sorted generics take only base-sorted inputs;
3. refinement lambdas occur only where elaboration can eliminate them;
4. Hindley generics occur in value-dependent positions, so application checking can solve every evar.

Generic instantiations have a ghost interpretation. Algorithmic checking elaborates implicit instantiations into
explicit ghost arguments before the soundness translation.

## refinedOCaml interfaces

The compiler-independent `refined_ocaml.ir` library now contains three layers.

### Refinement domain

`Refinement_domain.S` abstracts predicates, constraints, boolean composition, quantification, equality and
rendering. `Refinement_domain.Smt` is the current SMT-LIB string implementation. A future symbolic AST or Horn
domain can implement the same interface without changing the typing skeleton.

### Compositional typing judgment

`Typing_judgment.Make` is parameterized by a refinement domain and denotation. It supports syntax-directed
synthesis, branch composition, checking and explicit subsumption constraints. The two current denotations are:

```text
Safety:   assumptions ∧ actual ⇒ expected
Coverage: expected ⇒ assumptions ∧ actual
```

`Vc_semantics` uses these judgments in the production verification path. It is no longer responsible for
hard-coding the direction of refinement implication.

### Hindley evar context

`Evar_context.Make` provides first-order syntactic unification, recursive substitution, completeness queries and
an occurs-check. `Vc_backend` uses it for obligation-local polymorphic predicate/axiom instantiation. This is the
foundation corresponding to the paper's FA-hdl and ≡inst rules.

## Current boundary

This step establishes the compositional interface and migrates existing behavior onto it. It does not yet expose
surface syntax for higher-sorted generic refinement parameters and does not implement Horn-variable solving.

The next implementation slice should add:

1. refinement sorts and refinement terms, including first-order lambdas/applications;
2. schemes `forall generic. type` with explicit `Hindley` and `Horn` modes;
3. well-sortedness and polarity checking for the four invariants above;
4. function-application elaboration that introduces evars, checks arguments and requires a complete context;
5. beta reduction before SMT emission;
6. Horn constraint syntax and a solver only after Hindley schemes work end-to-end.

Coverage remains a distinct denotation. Sharing the syntax-directed skeleton does not justify silently reversing
all typing rules: witness scope, nondeterministic choice, recursion and effects still need mode-specific laws.

