# Upstream benchmark inventory

`manifest.tsv` is the reproducible input list for the LiquidHaskell tutorial and
CoverageType compatibility audits. Each row pins an upstream commit instead of
tracking a moving branch. `local_fixture` names the executable refinedOCaml
fixture. The benchmark test compiles those files, constructs every VC, and
requires all 40 positive obligations to be valid. It also requires all eleven
mutation controls to be invalid and executes runtime examples for every
CoverageType fixture.

These are original OCaml semantic ports, not verbatim copies. The LiquidHaskell
file selects one classic obligation from each tutorial chapter. The 29
CoverageType entries have executable predicates for their source invariants,
inverse-witness coverage obligations, runtime counterexamples, and mutation
controls for the major generator families. The manifest validator requires each
CoverageType row to name its exact semantic fixture and rejects
constant-false predicates and target-seed functions.

`coveragetype/boundlist.ml` and `coveragetype/duplicate_list.ml` are standalone
ports that preserve the recursive generator shape. Their size and element
parameters are universal coverage indices, and recursive calls use the
compositional under-summary checked by refinedOCaml.

- LiquidHaskell tutorial: <https://github.com/ucsd-progsys/liquidhaskell-tutorial>, BSD-3-Clause.
- CoverageType artifact (`jfp` branch): <https://github.com/OCamlRefinementType/CoverageType/tree/jfp>, MIT.

Refreshes must update the pinned revision and audit the diff before changing any
local fixture or support status.

Run the ports with `dune runtest benchmarks`.
