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

The non-recursive positive Horn slice is implemented. `[@@refined.horn]` schemes enforce that generic
applications occur only in top-level conjunctions and never in indices, negations, disjunctions or relations. At
application sites the solver collects lower bounds `A => P(t)`, abstracts `t` into a lambda parameter, and joins
multiple lower bounds with disjunction. The solution is substituted into result types, constraints and ghost
diagnostics. Constraints outside this fragment fail closed.

Elaborated Hindley/Horn result refinements now propagate through the SMT translation environment. ANF lets bind
the inferred type to the temporary symbol; variable lookup, local first-order inlining, and branches with equal
result refinements preserve it. Consequently only the first external value in a common generic call chain needs
an explicit `[@refined.type]`.

Horn solving now builds a predicate dependency graph and Tarjan SCCs, initializes every predicate to `false`,
and synchronously iterates the immediate-consequence operator to a least structural fixpoint. Base facts
propagate through mutually recursive SCCs; unfounded cycles remain false; a configurable iteration limit makes
non-convergence fail closed. The property fuzzer compares random Horn graphs against ordinary graph
reachability. This is a symbolic fixpoint for the supported positive term algebra, not a widening-based solver
for arbitrary SMT-CHCs.

The function-summary slice is now implemented for safety checking. Stable Core call graphs are decomposed with
Tarjan SCCs; recursive edges use independently checked over-contract summaries and emit path-sensitive
non-negativity and strict-decrease obligations for an `int` parameter measure. Coverage recursion remains
rejected because a whole-image coverage contract is not a compositional summary for a fixed call.

Checked signature lemmas and verification-artifact export are now implemented. Lemma VCs are checked in source
order against trusted axioms and earlier checked lemmas. `.rmi` v3 records the VC digest, solver identity,
timeout and dependency lists separately from trusted-axiom provenance; invalid or unknown lemmas fail before
atomic artifact export.
This is an auditable verification record, not a kernel-checkable Z3 proof certificate.

Use-site monomorphisation for parameterized user ADTs is now implemented. Closed instances are collected per
obligation, constructor families are keyed by result sort, recursive fields are substituted, and polymorphic
first-order inline calls instantiate their complete Core body. Open ADT instances fail closed.

Dependency-driven ADT/axiom slicing is now implemented as a least closure over contract/Core/summary roots,
statement symbols, and checked-lemma artifact dependencies. Logic declarations, provenance, proof artifacts
and complete ADT bundles are filtered together; an ADT used only as a value sort stays opaque. Random dependency
graphs are checked against an independent fixed-point oracle.

The typed Logic AST and expected-sort elaboration are now implemented. Equality propagates operand sorts in
both directions, constructors resolve from expected result and argument sorts, fields resolve from receiver
sorts, and SMT translation plus theory slicing consume the same resolved symbols.

Module aliases and monomorphic abstract-type theories are now implemented. Abstract sorts use lexical scope and
the same stable identity as client Typedtree types; signature and local aliases resolve through longest-prefix
path rewriting and recursive alias chains.

Functor theory transformers are now implemented for named first-order and unit functors. Named applications
use applicative `F(Arg)` sort identities; unit applications use fresh target paths. Result predicates/axioms and
parameter aliases are instantiated at applications, and `.rmi` v5 exports the templates.

Compositional coverage calls and witness-carrying under-summaries are now implemented. A complete mapping from
formal parameters to result-indexed inverse terms strengthens the whole-image existential VC into a constructive
certificate. Callers existentially choose call results and assume callee postconditions plus argument/witness
equalities; recursive calls additionally carry path-sensitive measure constraints. Contracts without witnesses
retain the old whole-image meaning and cannot summarize recursive calls.

The next implementation slice is relational state/outcome semantics for mutation, exceptions and effects.

Coverage remains a distinct denotation. Sharing the syntax-directed skeleton does not justify silently reversing
all typing rules: witness scope, nondeterministic choice, recursion and effects still need mode-specific laws.

## Property fuzzing

`test/fuzz_runner.ml` recursively generates ground/template term trees, higher-sorted predicate lambdas,
random mutually-recursive Horn graphs, and random function call graphs. It checks that successful unification
reconstructs the ground term, solved contexts are complete, recursive evar solutions fail the occurs-check,
Hindley application elaboration
returns the expected ghost argument, result substitution/beta-reduction preserve the generated scheme, and Horn
least-fixpoint solutions agree with graph reachability, and function SCCs agree with transitive closure. The
default seed and case count are deterministic; both
can be overridden through `REFINED_FUZZ_SEED` and `REFINED_FUZZ_CASES`.
