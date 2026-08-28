# OCaml compiler boundary

refinedOCaml consumes compiler-libs data structures stored in `.cmt/.cmti` files. These structures and their
binary representation are not stable across OCaml releases.

## Supported version

The current frontend supports exactly OCaml 5.3.0. This is enforced in four places:

- `refined_ocaml.opam` constrains the compiler to `= 5.3.0`;
- `refined_ocaml.opam.locked` records the tested direct dependencies;
- `dev/setup-switch.sh` creates or selects a 5.3.0 switch;
- the versioned frontend rejects a runtime compiler-version mismatch.

An `.rmi` also records `Sys.ocaml_version` and the corresponding `.cmi` digest. A client rejects an `.rmi`
produced by another compiler version or from a stale interface.

The current `.rmi` format version is 5. It separates trusted axioms from checked lemmas, stores a verification
artifact for every lemma, and exports abstract-sort/module-alias/functor-template metadata. Older formats are
rejected rather than decoded as if they carried this provenance.

## Upgrade procedure

Supporting a new compiler release requires a new frontend module rather than conditional patterns spread through
the semantic checker:

1. add `Ocaml_<major>_<minor>_frontend` for the release;
2. update Typedtree lowering tests and `.cmt/.cmti` fixtures;
3. run the complete safety, coverage, theory, stale-interface, and fail-closed suite;
4. regenerate the lock file with `opam lock --direct-only .`;
5. add a CI matrix entry only after the new frontend passes the same contract.

The stable Core and VC semantics must not contain `Typedtree`, `Types`, `Path`, `Ident`, `Shape`, or
`Cmt_format` values. Source locations are converted at the frontend boundary.
