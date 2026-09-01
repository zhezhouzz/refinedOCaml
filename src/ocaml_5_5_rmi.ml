open Refined_ir
open Refined_common

type typed_rmi = {
  format_version : int;
  ocaml_version : string;
  unit_name : string;
  interface_digest : string option;
  logic_symbols : (string * Typed_core.logic_symbol) list;
  abstract_sorts : (string * Typed_core.sort) list;
  module_aliases : (string * string) list;
  functor_theories : (string * Typed_core.functor_theory) list;
  generic_schemes : (string * Generic_refinement.scheme) list;
  axioms : Typed_core.axiom list;
  checked_lemmas : Typed_core.axiom list;
  proof_artifacts : Refined_types.proof_artifact list;
}

let current_rmi_version = 6

let read_rmi path =
  let channel = open_in_bin path in
  let rmi : typed_rmi =
    Fun.protect
      ~finally:(fun () -> close_in channel)
      (fun () -> Marshal.from_channel channel)
  in
  if rmi.format_version <> current_rmi_version then
    typed_error ~loc:Location.none "unsupported .rmi format version in `%s`"
      path;
  if rmi.ocaml_version <> Sys.ocaml_version then
    typed_error ~loc:Location.none
      ".rmi `%s` was produced by OCaml %s, but the checker uses OCaml %s" path
      rmi.ocaml_version Sys.ocaml_version;
  let lemma_names =
    List.map
      (fun (lemma : Typed_core.axiom) -> lemma.axiom_name)
      rmi.checked_lemmas
  in
  let artifact_names =
    List.map
      (fun (artifact : Refined_types.proof_artifact) -> artifact.lemma_name)
      rmi.proof_artifacts
  in
  if lemma_names <> artifact_names then
    typed_error ~loc:Location.none
      ".rmi `%s` has inconsistent checked-lemma artifacts" path;
  List.iter2
    (fun lemma artifact ->
      if
        artifact.Refined_types.statement
        <> Proof_artifact_io.canonical_statement lemma
        || artifact.statement_digest <> Proof_artifact_io.statement_digest lemma
      then
        typed_error ~loc:Location.none
          ".rmi `%s` has a statement digest mismatch for lemma `%s`" path
          artifact.lemma_name)
    rmi.checked_lemmas rmi.proof_artifacts;
  let trusted_axioms =
    List.map (fun (axiom : Typed_core.axiom) -> axiom.axiom_name) rmi.axioms
  in
  let rec validate_artifacts checked = function
    | [] -> ()
    | (artifact : Refined_types.proof_artifact) :: rest ->
        let subset members available =
          List.for_all (fun member -> List.mem member available) members
        in
        if
          (not (subset artifact.trusted_axioms trusted_axioms))
          || (not (subset artifact.checked_dependencies checked))
          || artifact.vc_digest = "" || artifact.solver = ""
          || artifact.artifact_version <> 1
          || artifact.statement = ""
          || artifact.statement_digest
             <> Proof_artifact_io.sha256 artifact.statement
          || artifact.digest_algorithm <> "sha256"
          || artifact.vc_smt = ""
          || artifact.vc_digest <> Proof_artifact_io.sha256 artifact.vc_smt
          || artifact.timeout_seconds <= 0
        then
          typed_error ~loc:Location.none
            ".rmi `%s` has malformed verification metadata for lemma `%s`" path
            artifact.lemma_name;
        validate_artifacts (checked @ [ artifact.lemma_name ]) rest
  in
  validate_artifacts [] rmi.proof_artifacts;
  let proof_path = path ^ ".rpa" in
  if not (Sys.file_exists proof_path) then
    typed_error ~loc:Location.none
      ".rmi `%s` is missing stable proof artifact sidecar `%s`" path proof_path;
  let bundle =
    try Proof_artifact_io.read proof_path
    with Invalid_argument message ->
      typed_error ~loc:Location.none
        "cannot parse proof artifact sidecar `%s`: %s" proof_path message
  in
  (match Proof_artifact_io.validate bundle with
  | Ok () -> ()
  | Error message ->
      typed_error ~loc:Location.none
        "proof artifact sidecar `%s` is invalid: %s" proof_path message);
  if
    bundle.unit_name <> rmi.unit_name
    || bundle.interface_digest <> rmi.interface_digest
    || bundle.artifacts <> rmi.proof_artifacts
  then
    typed_error ~loc:Location.none
      ".rmi `%s` does not match stable proof artifact sidecar" path;
  rmi

let write_rmi ~ensure_supported_version ~new_registry
    ~register_signature_theories ~verify ~cmti ~output =
  ensure_supported_version ();
  let cmt = Cmt_format.read_cmt cmti in
  let signature =
    match cmt.cmt_annots with
    | Cmt_format.Interface signature -> signature
    | _ ->
        typed_error ~loc:Location.none "`%s` is not a complete .cmti interface"
          cmti
  in
  let registry : Typed_core.registry = new_registry () in
  register_signature_theories registry ~root:cmt.cmt_modname signature;
  let seen = Hashtbl.create 16 in
  let hidden_by_functor name =
    Hashtbl.fold
      (fun _ (theory : Typed_core.functor_theory) hidden ->
        hidden
        || name = theory.result_prefix
        || String.starts_with ~prefix:(theory.result_prefix ^ ".") name)
      registry.functor_theories false
  in
  let logic_symbols =
    Hashtbl.fold
      (fun name (logic_symbol : Typed_core.logic_symbol) entries ->
        if
          logic_symbol.logic_name.key = "logic." ^ name
          && (not (hidden_by_functor name))
          && not (Hashtbl.mem seen logic_symbol.logic_name.key)
        then (
          Hashtbl.add seen logic_symbol.logic_name.key ();
          (name, logic_symbol) :: entries)
        else entries)
      registry.logic_by_name []
  in
  let generic_schemes =
    let prefix = cmt.cmt_modname ^ "." in
    Hashtbl.fold
      (fun name scheme entries ->
        if String.starts_with ~prefix name && not (hidden_by_functor name) then
          (name, scheme) :: entries
        else entries)
      registry.generic_schemes_by_name []
  in
  let prefix = cmt.cmt_modname ^ "." in
  let abstract_sorts =
    Hashtbl.fold
      (fun name sort entries ->
        if String.starts_with ~prefix name && not (hidden_by_functor name) then
          (name, sort) :: entries
        else entries)
      registry.abstract_sorts_by_name []
  in
  let module_aliases =
    Hashtbl.fold
      (fun name target entries ->
        if String.starts_with ~prefix name && not (hidden_by_functor name) then
          (name, target) :: entries
        else entries)
      registry.module_aliases []
  in
  let functor_theories =
    Hashtbl.fold
      (fun name theory entries ->
        if String.starts_with ~prefix name then (name, theory) :: entries
        else entries)
      registry.functor_theories []
  in
  let checked_lemmas = List.rev registry.lemmas in
  let proof_artifacts = verify registry checked_lemmas in
  let artifact_names =
    List.map
      (fun (artifact : Refined_types.proof_artifact) -> artifact.lemma_name)
      proof_artifacts
  in
  let lemma_names =
    List.map (fun (lemma : Typed_core.axiom) -> lemma.axiom_name) checked_lemmas
  in
  let statement_names =
    lemma_names
    @ List.map
        (fun (axiom : Typed_core.axiom) -> axiom.axiom_name)
        (List.rev registry.axioms)
  in
  if
    List.length statement_names
    <> List.length (List.sort_uniq String.compare statement_names)
  then
    typed_error ~loc:Location.none
      "theory `%s` exports duplicate axiom/lemma names" cmt.cmt_modname;
  if artifact_names <> lemma_names then
    typed_error ~loc:Location.none
      "internal error: lemma verification artifacts do not match declarations";
  let rmi =
    {
      format_version = current_rmi_version;
      ocaml_version = Sys.ocaml_version;
      unit_name = cmt.cmt_modname;
      interface_digest = Option.map Digest.to_hex cmt.cmt_interface_digest;
      logic_symbols;
      abstract_sorts;
      module_aliases;
      generic_schemes;
      axioms =
        List.rev registry.axioms
        |> List.filter (fun (axiom : Typed_core.axiom) ->
            not (hidden_by_functor axiom.axiom_name));
      checked_lemmas;
      proof_artifacts;
      functor_theories;
    }
  in
  let temporary =
    Filename.temp_file ~temp_dir:(Filename.dirname output)
      (Filename.basename output ^ ".")
      ".tmp"
  in
  let () =
    match
      let channel = open_out_bin temporary in
      Fun.protect
        ~finally:(fun () -> close_out channel)
        (fun () -> Marshal.to_channel channel rmi [])
    with
    | () -> Sys.rename temporary output
    | exception exception_ ->
        (try Sys.remove temporary with Sys_error _ -> ());
        raise exception_
  in
  Proof_artifact_io.write ~path:(output ^ ".rpa")
    {
      unit_name = rmi.unit_name;
      interface_digest = rmi.interface_digest;
      artifacts = rmi.proof_artifacts;
    }

let load_rmi_into registry cmt path =
  let rmi = read_rmi path in
  let imported = List.assoc_opt rmi.unit_name cmt.Cmt_format.cmt_imports in
  (match imported with
  | None ->
      typed_error ~loc:Location.none
        "theory `%s` belongs to module `%s`, which this implementation does \
         not import"
        path rmi.unit_name
  | Some _ -> ());
  let imported_digest = Option.join imported |> Option.map Digest.to_hex in
  (match (rmi.interface_digest, imported_digest) with
  | Some expected, Some actual when expected <> actual ->
      typed_error ~loc:Location.none
        "stale theory `%s`: interface digest does not match the imported .cmi"
        path
  | _ -> ());
  List.iter
    (fun (name, logic_symbol) ->
      Hashtbl.replace registry.Typed_core.logic_by_name name logic_symbol;
      let short = logic_symbol.Typed_core.logic_name.display in
      if not (Hashtbl.mem registry.logic_by_name short) then
        Hashtbl.add registry.logic_by_name short logic_symbol)
    rmi.logic_symbols;
  List.iter
    (fun (name, sort) ->
      Hashtbl.replace registry.Typed_core.abstract_sorts_by_name name sort;
      let short =
        match List.rev (String.split_on_char '.' name) with
        | short :: _ -> short
        | [] -> name
      in
      if not (Hashtbl.mem registry.abstract_sorts_by_name short) then
        Hashtbl.add registry.abstract_sorts_by_name short sort)
    rmi.abstract_sorts;
  List.iter
    (fun (name, target) ->
      Hashtbl.replace registry.Typed_core.module_aliases name target;
      let short =
        match List.rev (String.split_on_char '.' name) with
        | short :: _ -> short
        | [] -> name
      in
      if not (Hashtbl.mem registry.module_aliases short) then
        Hashtbl.add registry.module_aliases short target)
    rmi.module_aliases;
  List.iter
    (fun (name, theory) ->
      Hashtbl.replace registry.Typed_core.functor_theories name theory)
    rmi.functor_theories;
  List.iter
    (fun (name, scheme) ->
      Hashtbl.replace registry.Typed_core.generic_schemes_by_name name scheme;
      let short =
        match List.rev (String.split_on_char '.' name) with
        | short :: _ -> short
        | [] -> name
      in
      if not (Hashtbl.mem registry.generic_schemes_by_name short) then
        Hashtbl.add registry.generic_schemes_by_name short scheme)
    rmi.generic_schemes;
  registry.axioms <- List.rev_append rmi.axioms registry.axioms;
  registry.checked_lemmas <-
    List.rev_append rmi.checked_lemmas registry.checked_lemmas;
  registry.proof_artifacts <-
    List.rev_append rmi.proof_artifacts registry.proof_artifacts
