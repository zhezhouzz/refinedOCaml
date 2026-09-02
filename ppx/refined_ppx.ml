open Ppxlib

let is_refined attribute =
  match attribute.attr_name.txt with
  | "refined.over" | "refined.coverage" | "refined.measure" -> true
  | _ -> false

let validate_contract attribute =
  match attribute.attr_name.txt with
  | "refined.over" | "refined.coverage" -> (
      match attribute.attr_payload with
      | PStr
          [
            {
              pstr_desc =
                Pstr_eval ({ pexp_desc = Pexp_record (fields, None); _ }, _);
              _;
            };
          ] ->
          let names =
            List.map (fun ({ txt; _ }, _) -> Longident.last_exn txt) fields
          in
          let supported_fields =
            [
              "type_";
              "witnesses";
              "witness_relation";
              "ghosts";
              "raises";
              "performs";
              "outcomes";
              "state";
              "modifies";
              "requires_state";
              "state_witnesses";
              "result_state";
              "result_fresh";
              "result_references";
              "result_fresh_references";
              "result_reference_permissions";
              "result_recursive";
              "result_region";
              "requires_regions";
              "consumes_regions";
              "outcome_state";
              "outcome_modifies";
            ]
          in
          List.iter
            (fun name ->
              if not (List.mem name supported_fields) then
                Location.raise_errorf ~loc:attribute.attr_loc
                  "unknown refined contract field `%s`" name)
            names;
          if not (List.mem "type_" names) then
            Location.raise_errorf ~loc:attribute.attr_loc
              "refined contract requires the Liquid-style string field type_"
      | _ ->
          Location.raise_errorf ~loc:attribute.attr_loc
            "expected [@refined.%s { type_ = \"x:int -> {v:int | ...}\" }]"
            (if attribute.attr_name.txt = "refined.over" then "over"
             else "coverage"))
  | "refined.measure" -> (
      match attribute.attr_payload with
      | PStr
          [
            {
              pstr_desc =
                Pstr_eval
                  ({ pexp_desc = Pexp_constant (Pconst_string (_, _, _)); _ }, _);
              _;
            };
          ] ->
          ()
      | _ ->
          Location.raise_errorf ~loc:attribute.attr_loc
            "expected [@refined.measure \"integer_parameter\"]")
  | _ -> ()

class mapper =
  object
    inherit Ast_traverse.map as super

    method! attributes attributes =
      List.iter validate_contract (List.filter is_refined attributes);
      (* Refinement checking runs after OCaml's normal type checker, from the
         Typedtree stored in .cmt/.cmti files.  Custom attributes are therefore
         deliberately preserved here. *)
      super#attributes attributes
  end

let () =
  Driver.register_transformation "refined_ocaml" ~impl:(fun structure ->
      (new mapper)#structure structure)
