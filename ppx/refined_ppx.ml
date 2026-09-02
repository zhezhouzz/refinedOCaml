open Ppxlib

let is_refined attribute =
  match attribute.attr_name.txt with
  | "refined.over" | "refined.under" | "refined.coverage" | "refined.measure" ->
      true
  | _ -> false

let validate_contract attribute =
  match attribute.attr_name.txt with
  | "refined.over" | "refined.under" | "refined.coverage" -> (
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
          if not (List.mem "pre" names && List.mem "post" names) then
            Location.raise_errorf ~loc:attribute.attr_loc
              "refined contract requires string fields pre and post"
      | _ ->
          Location.raise_errorf ~loc:attribute.attr_loc
            "expected [@refined.%s { pre = \"...\"; post = \"...\" }]"
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
