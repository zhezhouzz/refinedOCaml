open Refined_ir
open Refined_types

type bundle = {
  unit_name : string;
  interface_digest : string option;
  artifacts : proof_artifact list;
}

let sha256 input = Digestif.SHA256.digest_string input |> Digestif.SHA256.to_hex

let canonical_statement (axiom : Typed_core.axiom) =
  let buffer = Buffer.create 256 in
  let field value =
    Buffer.add_string buffer (string_of_int (String.length value));
    Buffer.add_char buffer ':';
    Buffer.add_string buffer value;
    Buffer.add_char buffer ','
  in
  let rec sort = function
    | Typed_core.S_int -> field "int"
    | S_bool -> field "bool"
    | S_unit -> field "unit"
    | S_var variable ->
        field "var";
        field variable
    | S_tuple elements ->
        field "tuple";
        field (string_of_int (List.length elements));
        List.iter sort elements
    | S_app (symbol, arguments) ->
        field "app";
        field symbol.key;
        field (string_of_int (List.length arguments));
        List.iter sort arguments
  in
  field axiom.axiom_name;
  field (string_of_int (List.length axiom.scope));
  List.iter field axiom.scope;
  field (string_of_int (List.length axiom.variables));
  List.iter
    (fun (name, variable_sort) ->
      field name;
      sort variable_sort)
    axiom.variables;
  field axiom.body;
  Buffer.contents buffer

let statement_digest axiom = sha256 (canonical_statement axiom)

let add_netstring buffer value =
  Buffer.add_string buffer (string_of_int (String.length value));
  Buffer.add_char buffer ':';
  Buffer.add_string buffer value;
  Buffer.add_char buffer ','

let add_int buffer value = add_netstring buffer (string_of_int value)

let add_list buffer values =
  add_int buffer (List.length values);
  List.iter (add_netstring buffer) values

let encode bundle =
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer "RPA1\n";
  add_netstring buffer bundle.unit_name;
  add_netstring buffer (Option.value ~default:"" bundle.interface_digest);
  add_int buffer (List.length bundle.artifacts);
  List.iter
    (fun artifact ->
      add_int buffer artifact.artifact_version;
      add_netstring buffer artifact.lemma_name;
      add_netstring buffer artifact.statement;
      add_netstring buffer artifact.statement_digest;
      add_netstring buffer artifact.digest_algorithm;
      add_netstring buffer artifact.vc_digest;
      add_netstring buffer artifact.vc_smt;
      add_netstring buffer artifact.solver;
      add_int buffer artifact.timeout_seconds;
      add_list buffer artifact.trusted_axioms;
      add_list buffer artifact.checked_dependencies)
    bundle.artifacts;
  Buffer.contents buffer

let write ~path bundle =
  let temporary =
    Filename.temp_file ~temp_dir:(Filename.dirname path)
      (Filename.basename path ^ ".")
      ".tmp"
  in
  let channel = open_out_bin temporary in
  match
    Fun.protect
      ~finally:(fun () -> close_out channel)
      (fun () -> output_string channel (encode bundle))
  with
  | () -> Sys.rename temporary path
  | exception exception_ ->
      (try Sys.remove temporary with Sys_error _ -> ());
      raise exception_

let read_all path =
  let channel = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in channel)
    (fun () -> really_input_string channel (in_channel_length channel))

let read path =
  let input = read_all path in
  if not (String.starts_with ~prefix:"RPA1\n" input) then
    invalid_arg "unsupported proof artifact header";
  let cursor = ref 5 in
  let netstring () =
    let colon =
      try String.index_from input !cursor ':'
      with Not_found -> invalid_arg "truncated proof artifact length"
    in
    let length =
      try int_of_string (String.sub input !cursor (colon - !cursor))
      with Failure _ -> invalid_arg "invalid proof artifact length"
    in
    let start = colon + 1 in
    let finish = start + length in
    if finish >= String.length input || input.[finish] <> ',' then
      invalid_arg "truncated proof artifact value";
    cursor := finish + 1;
    String.sub input start length
  in
  let integer () =
    try int_of_string (netstring ())
    with Failure _ -> invalid_arg "invalid proof artifact integer"
  in
  let list () = List.init (integer ()) (fun _ -> netstring ()) in
  let unit_name = netstring () in
  let interface_digest =
    match netstring () with "" -> None | digest -> Some digest
  in
  let artifacts =
    List.init (integer ()) (fun _ ->
        let artifact_version = integer () in
        let lemma_name = netstring () in
        let statement = netstring () in
        let statement_digest = netstring () in
        let digest_algorithm = netstring () in
        let vc_digest = netstring () in
        let vc_smt = netstring () in
        let solver = netstring () in
        let timeout_seconds = integer () in
        let trusted_axioms = list () in
        let checked_dependencies = list () in
        {
          artifact_version;
          lemma_name;
          statement;
          statement_digest;
          digest_algorithm;
          vc_digest;
          vc_smt;
          solver;
          timeout_seconds;
          trusted_axioms;
          checked_dependencies;
        })
  in
  if !cursor <> String.length input then
    invalid_arg "trailing proof artifact data";
  { unit_name; interface_digest; artifacts }

let validate bundle =
  let rec check seen = function
    | [] -> Ok ()
    | artifact :: rest ->
        let fail message = Error (artifact.lemma_name ^ ": " ^ message) in
        if artifact.artifact_version <> 1 then
          fail "unsupported artifact version"
        else if artifact.statement_digest <> sha256 artifact.statement then
          fail "statement digest mismatch"
        else if artifact.digest_algorithm <> "sha256" then
          fail "unsupported digest algorithm"
        else if artifact.vc_digest <> sha256 artifact.vc_smt then
          fail "VC digest mismatch"
        else if artifact.timeout_seconds <= 0 || artifact.solver = "" then
          fail "invalid solver metadata"
        else if List.mem artifact.lemma_name seen then fail "duplicate lemma"
        else if
          not
            (List.for_all
               (fun dependency -> List.mem dependency seen)
               artifact.checked_dependencies)
        then fail "dependency is missing or out of order"
        else check (artifact.lemma_name :: seen) rest
  in
  if bundle.unit_name = "" then Error "proof bundle has no unit name"
  else check [] bundle.artifacts
