open Refined_ir
open Refined_types
open Parsetree
open Asttypes

let error ~loc format = Location.raise_errorf ~loc ("refinedOCaml: " ^^ format)

let source_position (position : Lexing.position) =
  Source_span.
    {
      offset = position.pos_cnum;
      line = position.pos_lnum;
      column = position.pos_cnum - position.pos_bol;
    }

let span_of_location (location : Location.t) =
  Source_span.
    {
      file = location.loc_start.pos_fname;
      start = source_position location.loc_start;
      finish = source_position location.loc_end;
    }

let lexing_position file (position : Source_span.position) =
  Lexing.
    {
      pos_fname = file;
      pos_lnum = position.line;
      pos_bol = position.offset - position.column;
      pos_cnum = position.offset;
    }

let location_of_span (span : Source_span.t) =
  Location.
    {
      loc_start = lexing_position span.file span.start;
      loc_end = lexing_position span.file span.finish;
      loc_ghost = false;
    }

let typed_error ~loc format =
  Location.raise_errorf ~loc ("refinedOCaml typed frontend: " ^^ format)

let typed_error_at span format = typed_error ~loc:(location_of_span span) format

let smt_identifier name =
  String.map
    (function
      | ('a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_') as character -> character
      | _ -> '_')
    name

let longident_last id = Longident.last id
let qualified_name scope name = String.concat "." (scope @ [ name ])

let rec longident_name = function
  | Longident.Lident name -> name
  | Ldot (prefix, name) -> longident_name prefix ^ "." ^ name
  | Lapply (left, right) ->
      longident_name left ^ "(" ^ longident_name right ^ ")"

let string_constant expression =
  match expression.pexp_desc with
  | Pexp_constant { pconst_desc = Pconst_string (value, _, _); _ } -> value
  | _ -> error ~loc:expression.pexp_loc "contract fields must be strings"

let contract_of_attribute attribute =
  let mode =
    match attribute.attr_name.txt with
    | "refined.over" -> Some Over
    | "refined.under" | "refined.coverage" -> Some Under
    | _ -> None
  in
  match mode with
  | None -> None
  | Some mode -> (
      match attribute.attr_payload with
      | PStr
          [
            {
              pstr_desc =
                Pstr_eval ({ pexp_desc = Pexp_record (fields, None); _ }, _);
              _;
            };
          ] ->
          let find name =
            List.find_map
              (fun ({ txt; _ }, expression) ->
                if longident_last txt = name then
                  Some (string_constant expression)
                else None)
              fields
          in
          let required name =
            match find name with
            | Some value -> value
            | None ->
                error ~loc:attribute.attr_loc
                  "contract is missing the `%s` string field" name
          in
          Some (mode, required "pre", required "post")
      | _ ->
          error ~loc:attribute.attr_loc
            "expected [@%s { pre = \"...\"; post = \"...\" }]"
            attribute.attr_name.txt)

let app name arguments = "(" ^ String.concat " " (name :: arguments) ^ ")"

let and_ terms =
  match terms with [] -> "true" | [ term ] -> term | _ -> app "and" terms

let or_ terms =
  match terms with [] -> "false" | [ term ] -> term | _ -> app "or" terms

let binary_operator = function
  | "+" -> Some "+"
  | "-" -> Some "-"
  | "*" -> Some "*"
  | "/" -> Some "div"
  | "mod" -> Some "mod"
  | "=" -> Some "="
  | "<>" -> Some "distinct"
  | "<" -> Some "<"
  | "<=" -> Some "<="
  | ">" -> Some ">"
  | ">=" -> Some ">="
  | "&&" -> Some "and"
  | "||" -> Some "or"
  | "implies" -> Some "=>"
  | _ -> None

let parse_formula ~filename ~loc text =
  let lexbuf = Lexing.from_string text in
  Location.init lexbuf filename;
  try Parse.expression lexbuf
  with _ -> error ~loc "cannot parse refinement formula `%s`" text
