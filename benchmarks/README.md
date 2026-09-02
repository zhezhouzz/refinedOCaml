# Upstream benchmark inventory

`manifest.tsv` is the reproducible input list for the LiquidHaskell tutorial and
CoverageType compatibility audits. Each row pins an upstream commit instead of
tracking a moving branch. `local_fixture` names the executable refinedOCaml
adaptation. The benchmark test compiles those files, constructs every VC, and
requires all 40 positive obligations to be valid. It also requires the
LeftistHeap rank mutation to be invalid and executes semantic runtime examples.

These are original OCaml adaptations, not verbatim copies. The LiquidHaskell
file selects one classic obligation from each tutorial chapter. The CoverageType
file covers every listed assertion's result carrier and invariant. LeftistHeap
is a semantic port of the upstream generator: it checks the recursive
rank/depth invariant, inverse witnesses, a mutation control, and executable
examples. The remaining explicit target-seed adapters isolate the
under-refinement coverage judgment from source features that belong to the
upstream generator runtime.

- LiquidHaskell tutorial: <https://github.com/ucsd-progsys/liquidhaskell-tutorial>, BSD-3-Clause.
- CoverageType artifact (`jfp` branch): <https://github.com/OCamlRefinementType/CoverageType/tree/jfp>, MIT.

Refreshes must update the pinned revision and audit the diff before changing any
local fixture or support status.

Run the ports with `dune runtest benchmarks`.
