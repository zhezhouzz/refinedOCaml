#!/usr/bin/env bash
set -euo pipefail

switch_name="${1:-.}"
ocaml_package="ocaml-base-compiler.5.5.0"

if ! command -v opam >/dev/null 2>&1; then
  echo "error: opam is required" >&2
  exit 1
fi

switch_exists=false
if [ "${switch_name}" = "." ] && [ -d "_opam" ]; then
  switch_exists=true
elif opam switch list --short | grep -Fxq "${switch_name}"; then
  switch_exists=true
fi

if [ "${switch_exists}" = false ]; then
  opam switch create "${switch_name}" "${ocaml_package}" --yes
fi

eval "$(opam env --switch="${switch_name}" --set-switch)"

if [ "$(ocamlc -version)" != "5.5.0" ]; then
  echo "error: refinedOCaml requires OCaml 5.5.0; selected $(ocamlc -version)" >&2
  exit 1
fi

opam install . --deps-only --with-test --locked --yes

if ! command -v z3 >/dev/null 2>&1; then
  echo "error: z3 must be installed by the host package manager" >&2
  exit 1
fi

echo "refinedOCaml environment is ready"
printf 'run: eval "$(opam env --switch=%s --set-switch)"\n' "${switch_name}"
echo "then: dune build @refined"
