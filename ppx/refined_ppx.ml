open Ppxlib

let rec longident_last = function
  | Longident.Lident name | Ldot (_, name) -> name
  | Lapply (_, right) -> longident_last right

let is_refined attribute =
  match attribute.attr_name.txt with
  | "refined.over" | "refined.under" -> true
  | _ -> false

let validate_contract attribute =
  match attribute.attr_name.txt with
  | "refined.over" | "refined.under" -> (
      match attribute.attr_payload with
      | PStr
          [ { pstr_desc =
                Pstr_eval
                  ({ pexp_desc = Pexp_record (fields, None); _ }, _);
              _ } ] ->
          let names =
            List.map
              (fun ({ txt; _ }, _) -> longident_last txt)
              fields
          in
          if not (List.mem "pre" names && List.mem "post" names) then
            Location.raise_errorf ~loc:attribute.attr_loc
              "refined contract requires string fields pre and post"
      | _ ->
          Location.raise_errorf ~loc:attribute.attr_loc
            "expected [@refined.%s { pre = \"...\"; post = \"...\" }]"
            (if attribute.attr_name.txt = "refined.over" then "over" else "under"))
  | _ -> ()

class mapper =
  object
    inherit Ast_traverse.map as super

    method! attributes attributes =
      List.iter validate_contract (List.filter is_refined attributes);
      super#attributes (List.filter (fun attribute -> not (is_refined attribute)) attributes)
  end

let () =
  Driver.register_transformation "refined_ocaml"
    ~impl:(fun structure -> (new mapper)#structure structure)
