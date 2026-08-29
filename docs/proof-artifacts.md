# Stable proof artifacts and replay

refinedOCaml writes a stable proof bundle beside every `.rmi` theory cache. For `theory.rmi`, the bundle is
`theory.rmi.rpa`. The `.rmi` remains an OCaml-version-specific cache; verification provenance is anchored by the
sidecar.

## RPA1 encoding

The file starts with the ASCII header `RPA1\n`. Every following value is a netstring:

```text
decimal-byte-length ':' raw-bytes ','
```

Values occur in this fixed order:

1. compilation-unit name;
2. interface digest, or an empty string;
3. artifact count;
4. for each artifact: artifact version, lemma name, canonical typed statement, statement SHA-256, digest algorithm,
   VC SHA-256, complete SMT-LIB VC, solver identity, timeout, trusted-axiom names, and ordered checked dependencies.

The statement digest covers the lemma name, lexical scope, typed variables and body. The VC digest covers the
exact bytes sent to the solver. SHA-256 is provided by the audited `digestif` library rather than a local hash
implementation.

## Replay kernel

```sh
refined-ocaml --replay-proof theory.rmi.rpa
```

Replay performs three stages:

1. the bounded netstring parser rejects malformed, truncated or trailing data;
2. the structural kernel checks versions, SHA-256 digests, unique lemma names and dependency order;
3. every stored VC is re-solved with the current Z3 and must return `unsat`.

Loading a v6 `.rmi` requires its `.rpa`; unit name, interface digest, artifacts and canonical statement digests
must match. RPA1 is a reproducible replay record, not a native Z3 proof certificate: the final stage still trusts
the currently executed solver. A future certificate kernel can add another artifact version without changing the
RPA1 framing.
