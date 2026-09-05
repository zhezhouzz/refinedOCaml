# Upstream benchmark ports

`manifest.tsv` pins 11 LiquidHaskell tutorial chapters and 29 CoverageType
source files. Every row now maps to executable algorithm code; the former
invariant/image adapters have been replaced. A row identifies the operations
listed in [PORTS.md](PORTS.md), not every exercise in an upstream chapter.

The runner checks the exact inventory and obligation names, requires **133
positive obligations** (48 safety, 85 coverage) to be valid, and requires 11
separate SMT negative controls to be invalid. It runs concrete examples for all
27 fixture modules, detects 17 mutations of algorithm bodies, and reproduces
the upstream zipperposition construction-time stack overflow. `Unknown` and
timeouts fail the suite.

| Manifest status | Meaning |
| --- | --- |
| `algorithm-verified` | Executable operations with the properties and representation changes in PORTS.md. |
| `corrected-verified` | The port includes a deliberate correction to the upstream body; the original failure is also reproduced. |

Run `REFINED_SOLVER_TIMEOUT_SECONDS=60 opam exec -- dune runtest benchmarks`.
The timeout is a per-obligation ceiling, not permission to accept an unknown.
CI pins Z3 4.16.0 through `dev/z3-requirements.txt` and checks the executable
visible inside `opam exec`. Ubuntu's Z3 4.13.3 package times out on the red-black
tree obligation even with a 960-second limit; that limit applies to one solver
process, not the complete suite. To reproduce CI locally:

```sh
python3 -m venv /tmp/refined-z3
/tmp/refined-z3/bin/python -m pip install --only-binary=:all: -r dev/z3-requirements.txt
PATH="/tmp/refined-z3/bin:$PATH" REFINED_SOLVER_TIMEOUT_SECONDS=60 opam exec -- dune runtest benchmarks
```

The runner prints the solver version, per-obligation timeout, and timings for
obligations taking at least a second. Unexpected solver results also write
`benchmark-failure.smt2` in the runner's working directory; CI uploads that
file for reproduction with `z3 -T:60 benchmark-failure.smt2`.

Logical predicates have executable definitions. Their explicit trusted axioms
are decomposition and measure laws; this verifier does not automatically prove
those laws from their OCaml definitions. Runtime examples test the concrete
interpretation, including nontrivial trees, rejected paths, callback execution,
map updates, buffer writes, and generator alternatives. They do not establish
exhaustive coverage or prove the axioms.

Coverage is a lower bound on the image of a nondeterministic generator. It says
every target has a producing execution, not that every execution satisfies the
target. `[@refined.choose]` supplies arbitrary symbolic choices during checking;
its executable body supplies repeatable choices for runtime tests. Support is
checked, not probabilities. Explicit `Reject` represents upstream `Err` paths.
The 17 algorithm mutations are runtime counterexamples, not additional SMT
`Invalid` results; recursive quantified theories can time out on false goals.

The ports do not claim full upstream language or library parity. In particular,
Haskell laziness, arbitrary refinement-predicate polymorphism, IEEE float
semantics, allocation costs, and every tutorial exercise are outside these
contracts. See PORTS.md for each concrete adaptation and excluded operation.

Sources: [LiquidHaskell tutorial](https://github.com/ucsd-progsys/liquidhaskell-tutorial)
(BSD-3-Clause) and [CoverageType artifact](https://github.com/OCamlRefinementType/CoverageType/tree/jfp)
(MIT). Exact revisions and source paths are in the manifest. Refreshes must
audit source changes before updating the inventory or support status.
