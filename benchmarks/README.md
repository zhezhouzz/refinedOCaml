# Upstream benchmark inventory

`manifest.tsv` is the reproducible input list for the LiquidHaskell tutorial and
CoverageType compatibility audits. Each row pins an upstream commit instead of
tracking a moving branch. `local_fixture` names the executable refinedOCaml
adaptation. The benchmark test compiles those files, constructs every VC, and
requires all 40 obligations to be valid.

These are original OCaml adaptations, not verbatim copies. The LiquidHaskell
file selects one classic obligation from each tutorial chapter. The CoverageType
file covers every listed assertion's result carrier and invariant; its explicit
target-seed adapters isolate the under-refinement coverage judgment from source
features that belong to the upstream generator runtime.

- LiquidHaskell tutorial: <https://github.com/ucsd-progsys/liquidhaskell-tutorial>, BSD-3-Clause.
- CoverageType artifact (`jfp` branch): <https://github.com/OCamlRefinementType/CoverageType/tree/jfp>, MIT.

Refreshes must update the pinned revision and audit the diff before changing any
local fixture or support status.

Run the ports with `dune runtest benchmarks`.
