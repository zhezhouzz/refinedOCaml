open Refined_ir
open Refined_common

let supported_ocaml_version = "5.5.0"

let ensure_supported_version () =
  if Sys.ocaml_version <> supported_ocaml_version then
    Location.raise_errorf ~loc:Location.none
      "refinedOCaml frontend supports OCaml %s, but is running under OCaml %s"
      supported_ocaml_version Sys.ocaml_version

open Ocaml_5_5_lowering
open Ocaml_5_5_theory

let typed_program_of_structure ?registry structure =
  let registry = Option.value registry ~default:(new_typed_registry ()) in
  typed_register_types registry structure;
  typed_register_theories registry structure;
  typed_register_choices registry structure;
  let rec module_structure = function
    | { Typedtree.mod_desc = Typedtree.Tmod_structure structure; _ } ->
        Some structure
    | { mod_desc = Tmod_constraint (inner, _, _, _); _ } ->
        module_structure inner
    | _ -> None
  in
  let rec functions structure =
    List.concat_map
      (fun item ->
        match item.Typedtree.str_desc with
        | Typedtree.Tstr_value (_, bindings) ->
            List.filter_map (typed_function registry) bindings
        | Tstr_module binding ->
            Option.fold ~none:[] ~some:functions
              (module_structure binding.mb_expr)
        | Tstr_recmodule bindings ->
            List.concat_map
              (fun (binding : Typedtree.module_binding) ->
                Option.fold ~none:[] ~some:functions
                  (module_structure binding.mb_expr))
              bindings
        | _ -> [])
      structure.Typedtree.str_items
  in
  Typed_core.{ registry; functions = functions structure }

let write_rmi ~verify ~cmti ~output =
  Ocaml_5_5_rmi.write_rmi ~ensure_supported_version
    ~new_registry:new_typed_registry
    ~register_signature_theories:typed_register_signature_theories ~verify ~cmti
    ~output

let load_rmi_into = Ocaml_5_5_rmi.load_rmi_into

let program_of_cmt ~theories filename =
  ensure_supported_version ();
  let cmt = Cmt_format.read_cmt filename in
  match cmt.cmt_annots with
  | Cmt_format.Implementation structure ->
      let registry = new_typed_registry () in
      List.iter (load_rmi_into registry cmt) theories;
      typed_program_of_structure ~registry structure
  | Cmt_format.Interface _ ->
      typed_error ~loc:Location.none
        "expected a typed implementation .cmt, but received an interface"
  | Packed _ | Partial_implementation _ | Partial_interface _ ->
      typed_error ~loc:Location.none
        "expected a complete typed implementation .cmt; OCaml emitted only a \
         partial tree"
