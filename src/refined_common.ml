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
  | Ldot (prefix, name) -> longident_name prefix.txt ^ "." ^ name.txt
  | Lapply (left, right) ->
      longident_name left.txt ^ "(" ^ longident_name right.txt ^ ")"

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
          let find_expression name =
            List.find_map
              (fun ({ txt; _ }, expression) ->
                if longident_last txt = name then Some expression else None)
              fields
          in
          let find name = Option.map string_constant (find_expression name) in
          let required name =
            match find name with
            | Some value -> value
            | None ->
                error ~loc:attribute.attr_loc
                  "contract is missing the `%s` string field" name
          in
          let rec expression_list expression =
            match expression.pexp_desc with
            | Pexp_construct ({ txt = Lident "[]"; _ }, None) -> []
            | Pexp_construct
                ( { txt = Lident "::"; _ },
                  Some
                    { pexp_desc = Pexp_tuple [ (None, head); (None, tail) ]; _ }
                ) ->
                head :: expression_list tail
            | _ ->
                error ~loc:expression.pexp_loc
                  "contract witnesses must be an OCaml list literal"
          in
          let witnesses =
            match find_expression "witnesses" with
            | None -> []
            | Some expression ->
                expression_list expression
                |> List.map (fun expression ->
                    match expression.pexp_desc with
                    | Pexp_tuple [ (None, parameter); (None, witness) ] ->
                        (string_constant parameter, string_constant witness)
                    | _ ->
                        error ~loc:expression.pexp_loc
                          "coverage witnesses must contain (parameter, \
                           expression) string pairs")
          in
          let result_state = find "result_state" in
          let result_fresh =
            match find_expression "result_fresh" with
            | None -> false
            | Some
                {
                  pexp_desc = Pexp_construct ({ txt = Lident "true"; _ }, None);
                  _;
                } ->
                true
            | Some
                {
                  pexp_desc = Pexp_construct ({ txt = Lident "false"; _ }, None);
                  _;
                } ->
                false
            | Some expression ->
                error ~loc:expression.pexp_loc
                  "result_fresh must be a boolean literal"
          in
          let witness_relation = find "witness_relation" in
          let ghosts =
            match find_expression "ghosts" with
            | None -> []
            | Some expression ->
                expression_list expression
                |> List.map (fun expression ->
                    match expression.pexp_desc with
                    | Pexp_tuple [ (None, name); (None, sort) ] ->
                        let name = string_constant name in
                        let sort = string_constant sort in
                        (name, sort)
                    | _ ->
                        error ~loc:expression.pexp_loc
                          "ghosts must contain (name, sort) string pairs")
          in
          let raises =
            match find_expression "raises" with
            | None -> []
            | Some expression ->
                expression_list expression
                |> List.map (fun expression ->
                    match expression.pexp_desc with
                    | Pexp_tuple [ (None, exception_); (None, predicate) ] ->
                        (string_constant exception_, string_constant predicate)
                    | _ ->
                        error ~loc:expression.pexp_loc
                          "raises must contain (exception, predicate) string \
                           pairs")
          in
          let state =
            match find_expression "state" with
            | None -> []
            | Some expression ->
                expression_list expression
                |> List.map (fun expression ->
                    match expression.pexp_desc with
                    | Pexp_tuple [ (None, cell); (None, predicate) ] ->
                        (string_constant cell, string_constant predicate)
                    | _ ->
                        error ~loc:expression.pexp_loc
                          "state must contain (cell, predicate) string pairs")
          in
          let modifies =
            match find_expression "modifies" with
            | None -> []
            | Some expression ->
                List.map string_constant (expression_list expression)
          in
          let state_pairs field =
            match find_expression field with
            | None -> []
            | Some expression ->
                expression_list expression
                |> List.map (fun expression ->
                    match expression.pexp_desc with
                    | Pexp_tuple [ (None, cell); (None, predicate) ] ->
                        (string_constant cell, string_constant predicate)
                    | _ ->
                        error ~loc:expression.pexp_loc
                          "%s must contain (cell, expression) string pairs"
                          field)
          in
          let result_references = state_pairs "result_references" in
          let result_fresh_references =
            match find_expression "result_fresh_references" with
            | None -> []
            | Some expression ->
                List.map string_constant (expression_list expression)
          in
          let result_reference_permissions =
            state_pairs "result_reference_permissions"
          in
          let result_recursive =
            match find_expression "result_recursive" with
            | None -> false
            | Some
                {
                  pexp_desc = Pexp_construct ({ txt = Lident "true"; _ }, None);
                  _;
                } ->
                true
            | Some
                {
                  pexp_desc = Pexp_construct ({ txt = Lident "false"; _ }, None);
                  _;
                } ->
                false
            | Some expression ->
                error ~loc:expression.pexp_loc
                  "result_recursive must be a boolean literal"
          in
          let result_region = find "result_region" in
          let requires_regions = state_pairs "requires_regions" in
          let consumes_regions =
            match find_expression "consumes_regions" with
            | None -> []
            | Some expression ->
                List.map string_constant (expression_list expression)
          in
          let requires_state = state_pairs "requires_state" in
          let state_witnesses = state_pairs "state_witnesses" in
          let performs =
            match find_expression "performs" with
            | None -> []
            | Some expression ->
                expression_list expression
                |> List.map (fun expression ->
                    match expression.pexp_desc with
                    | Pexp_tuple [ (None, operation); (None, predicate) ] ->
                        (string_constant operation, string_constant predicate)
                    | _ ->
                        error ~loc:expression.pexp_loc
                          "performs must contain (operation, predicate) string \
                           pairs")
          in
          let string_pairs expression =
            expression_list expression
            |> List.map (fun expression ->
                match expression.pexp_desc with
                | Pexp_tuple [ (None, name); (None, value) ] ->
                    (string_constant name, string_constant value)
                | _ ->
                    error ~loc:expression.pexp_loc
                      "outcome witnesses must contain string pairs")
          in
          let outcomes =
            match find_expression "outcomes" with
            | None -> []
            | Some expression ->
                expression_list expression
                |> List.map (fun expression ->
                    match expression.pexp_desc with
                    | Pexp_tuple
                        [
                          (None, kind);
                          (None, name);
                          (None, post);
                          (None, witnesses);
                        ] ->
                        ( string_constant kind,
                          string_constant name,
                          string_constant post,
                          string_pairs witnesses,
                          None )
                    | Pexp_tuple
                        [
                          (None, kind);
                          (None, name);
                          (None, post);
                          (None, witnesses);
                          (None, relation);
                        ] ->
                        ( string_constant kind,
                          string_constant name,
                          string_constant post,
                          string_pairs witnesses,
                          Some (string_constant relation) )
                    | _ ->
                        error ~loc:expression.pexp_loc
                          "outcomes must contain (kind, name, post, witnesses) \
                           or (kind, name, post, witnesses, relation) tuples")
          in
          let outcome_state =
            match find_expression "outcome_state" with
            | None -> []
            | Some expression ->
                expression_list expression
                |> List.map (fun expression ->
                    match expression.pexp_desc with
                    | Pexp_tuple
                        [
                          (None, kind);
                          (None, name);
                          (None, cell);
                          (None, predicate);
                        ] ->
                        ( string_constant kind,
                          string_constant name,
                          string_constant cell,
                          string_constant predicate )
                    | _ ->
                        error ~loc:expression.pexp_loc
                          "outcome_state must contain (kind, name, cell, \
                           predicate) string tuples")
          in
          let outcome_modifies =
            match find_expression "outcome_modifies" with
            | None -> []
            | Some expression ->
                expression_list expression
                |> List.map (fun expression ->
                    match expression.pexp_desc with
                    | Pexp_tuple [ (None, kind); (None, name); (None, cell) ] ->
                        ( string_constant kind,
                          string_constant name,
                          string_constant cell )
                    | _ ->
                        error ~loc:expression.pexp_loc
                          "outcome_modifies must contain (kind, name, cell) \
                           string tuples")
          in
          if mode = Over && witnesses <> [] then
            error ~loc:attribute.attr_loc
              "safety contracts cannot declare coverage witnesses";
          if mode = Over && witness_relation <> None then
            error ~loc:attribute.attr_loc
              "safety contracts cannot declare witness_relation";
          if mode = Over && ghosts <> [] then
            error ~loc:attribute.attr_loc
              "safety contracts cannot declare ghosts";
          if witnesses <> [] && witness_relation <> None then
            error ~loc:attribute.attr_loc
              "coverage must choose functional witnesses or witness_relation";
          if ghosts <> [] && witnesses <> [] then
            error ~loc:attribute.attr_loc
              "ghosts require relational rather than functional witnesses";
          List.iter
            (fun (_, _, _, witnesses, relation) ->
              if witnesses <> [] && relation <> None then
                error ~loc:attribute.attr_loc
                  "coverage outcome must choose witnesses or relation";
              if ghosts <> [] && witnesses <> [] then
                error ~loc:attribute.attr_loc
                  "ghosts require relational outcome witnesses")
            outcomes;
          if
            ghosts <> [] && witness_relation = None
            && not
                 (List.exists
                    (fun (_, _, _, _, relation) -> relation <> None)
                    outcomes)
          then
            error ~loc:attribute.attr_loc
              "coverage ghosts require a witness relation";
          if mode = Under && raises <> [] then
            error ~loc:attribute.attr_loc
              "coverage contracts cannot yet declare raised outcomes";
          if mode = Over && state_witnesses <> [] then
            error ~loc:attribute.attr_loc
              "safety contracts cannot declare state witnesses";
          if mode = Under && performs <> [] then
            error ~loc:attribute.attr_loc
              "coverage performed-outcome witnesses are not yet supported";
          if mode = Over && outcomes <> [] then
            error ~loc:attribute.attr_loc
              "safety contracts cannot declare coverage outcomes";
          Some
            ( mode,
              required "pre",
              required "post",
              result_state,
              result_fresh,
              result_references,
              result_fresh_references,
              result_reference_permissions,
              result_recursive,
              result_region,
              requires_regions,
              consumes_regions,
              witnesses,
              witness_relation,
              ghosts,
              raises,
              state,
              modifies,
              requires_state,
              state_witnesses,
              performs,
              outcomes,
              outcome_state,
              outcome_modifies )
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
  | "==" -> Some "="
  | "!=" -> Some "distinct"
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
