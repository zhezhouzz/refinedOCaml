# Upstream benchmark inventory

`manifest.tsv` pins 11 LiquidHaskell tutorial chapters and 29 CoverageType
source files. **Inventory rows are not counts of fully ported algorithms.**
The runner checks the exact mapping, compiles every annotated fixture, and
requires all 52 positive obligations to be valid (19 safety, 33 coverage).
It separately requires 11 SMT mutation controls to be invalid, runs executable
examples for every CoverageType fixture and both LiquidHaskell algorithm
fixtures, and detects 8 mutations of the newly ported algorithm bodies at runtime.
`Unknown` does not count as a successful verification.

| Manifest status | Meaning |
| --- | --- |
| `algorithm-verified` | The named operation/generator runs its algorithm, with the properties and adaptations below. This does not claim every function in the upstream file is ported. |
| `adapted-verified` | One small illustrative safety obligation; not validation of the whole tutorial chapter. |
| `semantic-adapter` | An invariant/image adapter; not verification of the original recursive generator. |

## Algorithm ports

- `liquidhaskell/lazy_queue.ml`: rotation, smart construction, insertion,
  nonempty removal, and replication. Contracts check list/queue sizes and the
  back/front balance invariant. Runtime examples check FIFO order. Strict OCaml
  does not preserve the original Haskell lazy evaluation cost bound.
- `liquidhaskell/avl.ml`: cached-height construction, single/double rotations,
  and recursive insertion. Contracts check ordering within explicit integer
  intervals, AVL balance, cached heights, and insertion's height bound. Runtime
  examples check element preservation and all four rotations. Deletion is not
  ported; set preservation is not currently an SMT obligation.
- `coveragetype/boundlist.ml` and `duplicate_list.ml`: recursive generators with
  universal size/element indices and compositional recursive under-summaries.
- `coveragetype/leftist_heap.ml`: the recursive left/right generator with a
  universal depth index. An independently checked range-generator summary
  models `int_range_inc`; it avoids inlining the range clamp into the heap VC.
- `coveragetype/semantic_stlc.ml`: no-application generation and recursive
  application/abstraction generation. Context, target type, and application
  count remain universal indices. The proof uses a lexicographic application/
  arrow-count measure and preserves rejection paths. `gen_type` is the complete
  nondeterministic library primitive declared in upstream `gen_term_size.ml`.
  Variable generation uses an arbitrary index plus the original lookup filter;
  application nodes retain the type computed internally by the source.

Logical predicates have executable definitions. Their explicit trusted axioms
are inversion/measure laws, not automatically verified translations of their
OCaml bodies. Runtime examples exercise the concrete interpretation. Coverage
proofs use decomposition laws; recursive constructor-introduction laws are
unnecessary here and can cause unbounded SMT instantiation.

Coverage is a lower image bound: a particular runtime choice need not produce
exactly the requested application count. Runtime tests do not establish
exhaustive coverage; the quantified VCs do that. The 8 algorithm mutations are
runtime counterexamples, not claimed SMT `Invalid` results. Z3 can time out on
false goals involving quantified recursive theories.

The remaining nine tutorial representatives and 24 CoverageType adapters still
need further ports before claiming full upstream benchmark parity. For example,
`semantic_lists.ml` still accepts an existing tail instead of recursively
constructing it. The manifest no longer labels those rows as algorithm ports.

## Sources and execution

- LiquidHaskell tutorial: <https://github.com/ucsd-progsys/liquidhaskell-tutorial>, BSD-3-Clause.
- CoverageType artifact (`jfp` branch): <https://github.com/OCamlRefinementType/CoverageType/tree/jfp>, MIT.

These are OCaml adaptations at the revisions recorded in the manifest.
Refreshes must audit the pinned source changes before changing local fixtures or
support status. Run with `opam exec -- dune runtest benchmarks`.
