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

type surface_refined_base = {
  surface_value : string;
  surface_type : string;
  surface_predicate : string;
}

type surface_refined_type =
  | Surface_base of surface_refined_base
  | Surface_arrow of string * surface_refined_type * surface_refined_type

let trim = String.trim

let identifier_character = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
  | _ -> false

let rename_identifier ~from ~into text =
  let buffer = Buffer.create (String.length text) in
  let rec loop index =
    if index = String.length text then Buffer.contents buffer
    else if identifier_character text.[index] then (
      let finish = ref (index + 1) in
      while
        !finish < String.length text && identifier_character text.[!finish]
      do
        incr finish
      done;
      let token = String.sub text index (!finish - index) in
      Buffer.add_string buffer (if token = from then into else token);
      loop !finish)
    else (
      Buffer.add_char buffer text.[index];
      loop (index + 1))
  in
  loop 0

let find_top_level ?(arrow = false) character text =
  let length = String.length text in
  let rec loop index parentheses brackets braces =
    if index >= length then None
    else
      let current = text.[index] in
      if
        arrow && current = '-'
        && index + 1 < length
        && text.[index + 1] = '>'
        && parentheses = 0 && brackets = 0 && braces = 0
      then Some index
      else if
        (not arrow) && current = character && parentheses = 0 && brackets = 0
        && braces = 0
      then Some index
      else
        let parentheses, brackets, braces =
          match current with
          | '(' -> (parentheses + 1, brackets, braces)
          | ')' -> (parentheses - 1, brackets, braces)
          | '[' -> (parentheses, brackets + 1, braces)
          | ']' -> (parentheses, brackets - 1, braces)
          | '{' -> (parentheses, brackets, braces + 1)
          | '}' -> (parentheses, brackets, braces - 1)
          | _ -> (parentheses, brackets, braces)
        in
        if parentheses < 0 || brackets < 0 || braces < 0 then None
        else loop (index + 1) parentheses brackets braces
  in
  loop 0 0 0 0

let split_at index width text =
  ( String.sub text 0 index |> trim,
    String.sub text (index + width) (String.length text - index - width) |> trim
  )

let strip_outer_parentheses text =
  let text = trim text in
  let length = String.length text in
  if length < 2 || text.[0] <> '(' || text.[length - 1] <> ')' then text
  else
    let rec closes_at_end index depth =
      if index = length then depth = 0
      else
        let depth =
          match text.[index] with
          | '(' -> depth + 1
          | ')' -> depth - 1
          | _ -> depth
        in
        depth >= 0
        && (index = length - 1 || depth > 0)
        && closes_at_end (index + 1) depth
    in
    if closes_at_end 0 0 then String.sub text 1 (length - 2) |> trim else text

let parse_surface_base ~loc ~default_value text =
  let text = trim text in
  let length = String.length text in
  if length >= 2 && text.[0] = '{' && text.[length - 1] = '}' then
    let inner = String.sub text 1 (length - 2) |> trim in
    match find_top_level ':' inner with
    | None -> error ~loc "refined base `%s` is missing `:`" text
    | Some colon -> (
        let value, rest = split_at colon 1 inner in
        if value = "" then error ~loc "refined base has an empty value binder";
        match find_top_level '|' rest with
        | None -> error ~loc "refined base `%s` is missing `|`" text
        | Some pipe ->
            let type_, predicate = split_at pipe 1 rest in
            if type_ = "" || predicate = "" then
              error ~loc "refined base `%s` has an empty type or predicate" text;
            {
              surface_value = value;
              surface_type = type_;
              surface_predicate = predicate;
            })
  else if text = "" then error ~loc "refined type contains an empty base"
  else
    {
      surface_value = default_value;
      surface_type = text;
      surface_predicate = "true";
    }

let parse_surface_refined_type ~loc text =
  let rec parse text =
    let text = strip_outer_parentheses text in
    match find_top_level ~arrow:true '\000' text with
    | None ->
        Surface_base (parse_surface_base ~loc ~default_value:"result" text)
    | Some arrow -> (
        let parameter, codomain = split_at arrow 2 text in
        match find_top_level ':' parameter with
        | None ->
            error ~loc "refined function parameter `%s` is missing `:`"
              parameter
        | Some colon ->
            let name, domain = split_at colon 1 parameter in
            if name = "" then error ~loc "refined function has an empty binder";
            Surface_arrow (name, parse domain, parse codomain))
  in
  parse text

let contract_of_attribute attribute =
  let mode =
    match attribute.attr_name.txt with
    | "refined.over" -> Some Over
    | "refined.coverage" -> Some Under
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
            (fun ({ txt; loc }, _) ->
              let name = longident_last txt in
              if not (List.mem name supported_fields) then
                error ~loc "unknown refined contract field `%s`" name)
            fields;
          let find name = Option.map string_constant (find_expression name) in
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
          let surface_type =
            match find "type_" with
            | Some text ->
                parse_surface_refined_type ~loc:attribute.attr_loc text
            | None ->
                error ~loc:attribute.attr_loc
                  "contract is missing the Liquid-style `type_` string field"
          in
          Some
            ( mode,
              surface_type,
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
            "expected [@%s { type_ = \"x:int -> {v:int | ...}\" }]"
            attribute.attr_name.txt)

let app name arguments = "(" ^ String.concat " " (name :: arguments) ^ ")"

let and_ terms =
  match terms with [] -> "true" | [ term ] -> term | _ -> app "and" terms

let or_ terms =
  match terms with [] -> "false" | [ term ] -> term | _ -> app "or" terms

let smt_binders declarations =
  "("
  ^ String.concat " "
      (List.map
         (fun (name, sort) -> Printf.sprintf "(%s %s)" name sort)
         declarations)
  ^ ")"

let smt_quantify quantifier declarations formula =
  if declarations = [] then formula
  else app quantifier [ smt_binders declarations; formula ]

let smt_forall declarations formula = smt_quantify "forall" declarations formula
let smt_exists declarations formula = smt_quantify "exists" declarations formula

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
