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

### Hindley schemes and evar context

`Evar_context.Make` provides first-order syntactic unification, recursive substitution, completeness queries and
an occurs-check. `Generic_refinement` adds base/function refinement sorts, first-order refinement lambdas and
applications, `Hindley`/`Horn` generic modes, refined function schemes, well-formedness checking and explicit
application elaboration. Hindley applications create evars, unify them from value-dependent input indices,
require a complete context, emit ghost instantiations, substitute the result, and beta-reduce before returning it.

`Vc_backend` also uses the generic evar context for obligation-local polymorphic predicate/axiom instantiation.
Together these pieces correspond to the paper's FA-hdl and ≡inst rules.

## Current boundary

Higher-sorted Hindley schemes are now exposed through `[@@refined.hindley]` in `.mli` files and serialized in
`.rmi` version 2. Call arguments carry their current type through `[@refined.type]`. The versioned frontend parses
both attributes, and the VC backend runs elaboration for the resolved OCaml `Path`, emits an uninterpreted runtime
summary and checks elaborated side conditions. Ghost instantiations are retained in diagnostics.

The next implementation slice should add Horn constraint syntax, top-level positivity checking, Horn-variable
generation at application sites and a solver. Hindley result refinements should also be propagated to later Core
expressions so common call chains need fewer explicit `[@refined.type]` annotations.

Coverage remains a distinct denotation. Sharing the syntax-directed skeleton does not justify silently reversing
all typing rules: witness scope, nondeterministic choice, recursion and effects still need mode-specific laws.

## Property fuzzing

`test/fuzz_runner.ml` recursively generates ground/template term trees and higher-sorted predicate lambdas. It
checks that successful unification reconstructs the ground term, solved contexts are complete, recursive
solutions fail the occurs-check, Hindley application elaboration returns the expected ghost argument, and result
substitution/beta-reduction preserve the generated scheme. The default seed and case count are deterministic;
both can be overridden through `REFINED_FUZZ_SEED` and `REFINED_FUZZ_CASES`.
