open Parsetree
open Asttypes

type mode = Over | Under

type verdict =
  | Valid
  | Invalid of string
  | Unknown of string

type obligation = {
  name : string;
  mode : mode;
  location : Location.t;
  smt : string;
}

type sort = Int | Bool | Unit | User of string

type constructor = {
  smt_name : string;
  arguments : sort list;
}

type datatype = {
  type_name : string;
  constructors : constructor list;
}

type registry = {
  constructors : (string, constructor) Hashtbl.t;
  fields : (string, constructor * int) Hashtbl.t;
  datatypes : datatype list;
}

let mode_name = function Over -> "over" | Under -> "under"

let error ~loc format = Location.raise_errorf ~loc ("refinedOCaml: " ^^ format)

let smt_identifier name =
  String.map
    (function
      | ('a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_') as character -> character
      | _ -> '_')
    name

let smt_sort = function
  | Int -> "Int"
  | Bool -> "Bool"
  | Unit -> "Unit"
  | User name -> "T_" ^ smt_identifier name

let longident_last id = Longident.last id

let sort_of_core_type core_type =
  match core_type.ptyp_desc with
  | Ptyp_constr ({ txt; _ }, []) -> (
      match longident_last txt with
      | "int" -> Int
      | "bool" -> Bool
      | "unit" -> Unit
      | name -> User name)
  | _ ->
      error ~loc:core_type.ptyp_loc
        "the prototype requires a monomorphic first-order type annotation"

let string_constant expression =
  match expression.pexp_desc with
  | Pexp_constant { pconst_desc = Pconst_string (value, _, _); _ } -> value
  | _ -> error ~loc:expression.pexp_loc "contract fields must be strings"

let contract_of_attribute attribute =
  let mode =
    match attribute.attr_name.txt with
    | "refined.over" -> Some Over
    | "refined.under" -> Some Under
    | _ -> None
  in
  match mode with
  | None -> None
  | Some mode -> (
      match attribute.attr_payload with
      | PStr
          [ { pstr_desc =
                Pstr_eval
                  ({ pexp_desc = Pexp_record (fields, None); _ }, _);
              _ } ] ->
          let find name =
            List.find_map
              (fun ({ txt; _ }, expression) ->
                if longident_last txt = name then Some (string_constant expression)
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

let contract_of_attributes attributes =
  let contracts = List.filter_map contract_of_attribute attributes in
  match contracts with
  | [] -> None
  | [ contract ] -> Some contract
  | _ ->
      let attribute = List.hd attributes in
      error ~loc:attribute.attr_loc "a binding can have only one refinement contract"

let flatten_pattern pattern =
  match pattern.ppat_desc with
  | Ppat_tuple patterns -> patterns
  | _ -> [ pattern ]

let variable_of_pattern pattern =
  match pattern.ppat_desc with
  | Ppat_constraint (inner, core_type) -> (
      match inner.ppat_desc with
      | Ppat_var { txt = name; _ } -> (name, sort_of_core_type core_type)
      | _ ->
          error ~loc:pattern.ppat_loc
            "function arguments must be variables with type annotations")
  | Ppat_var { txt = name; _ } -> (name, Int)
  | _ ->
      error ~loc:pattern.ppat_loc
        "function arguments must be variables (annotate non-int arguments)"

let function_shape expression =
  match expression.pexp_desc with
  | Pexp_function (parameters, constraint_, Pfunction_body body) ->
      let arguments =
        List.map
          (fun parameter ->
            match parameter.pparam_desc with
            | Pparam_val (Nolabel, None, pattern) -> variable_of_pattern pattern
            | Pparam_val _ ->
                error ~loc:parameter.pparam_loc
                  "labelled and optional arguments are not in the first prototype"
            | Pparam_newtype _ ->
                error ~loc:parameter.pparam_loc
                  "locally abstract types are not in the first prototype")
          parameters
      in
      let result_sort =
        match constraint_ with
        | Some (Pconstraint core_type) -> sort_of_core_type core_type
        | Some (Pcoerce (_, core_type)) -> sort_of_core_type core_type
        | None -> Int
      in
      (arguments, result_sort, body)
  | _ ->
      error ~loc:expression.pexp_loc
        "a refined binding must be an explicitly written function"

let constructor_args declaration =
  match declaration.pcd_args with
  | Pcstr_tuple types -> List.map sort_of_core_type types
  | Pcstr_record labels -> List.map (fun label -> sort_of_core_type label.pld_type) labels

let register_types structure =
  let declarations =
    List.concat_map
      (fun item ->
        match item.pstr_desc with Pstr_type (_, declarations) -> declarations | _ -> [])
      structure
  in
  List.iter
    (fun declaration ->
      if declaration.ptype_params <> [] then
        error ~loc:declaration.ptype_loc
          "parametric datatype `%s` needs monomorphisation (planned, not silently approximated)"
          declaration.ptype_name.txt)
    declarations;
  let constructors_table = Hashtbl.create 32 in
  let fields_table = Hashtbl.create 32 in
  let datatypes =
    List.filter_map
      (fun declaration ->
        let owner = declaration.ptype_name.txt in
        let make_constructor ocaml_name arguments =
          let constructor =
            {
              smt_name = "C_" ^ smt_identifier owner ^ "_" ^ smt_identifier ocaml_name;
              arguments;
            }
          in
          Hashtbl.replace constructors_table ocaml_name constructor;
          constructor
        in
        match declaration.ptype_kind with
        | Ptype_variant declarations ->
            let constructors =
              List.map
                (fun constructor ->
                  make_constructor constructor.pcd_name.txt
                    (constructor_args constructor))
                declarations
            in
            Some { type_name = owner; constructors }
        | Ptype_record labels ->
            let constructor =
              make_constructor ("record_" ^ owner)
                (List.map (fun label -> sort_of_core_type label.pld_type) labels)
            in
            List.iteri
              (fun index label ->
                Hashtbl.replace fields_table label.pld_name.txt (constructor, index))
              labels;
            Some { type_name = owner; constructors = [ constructor ] }
        | Ptype_abstract | Ptype_open -> None)
      declarations
  in
  { constructors = constructors_table; fields = fields_table; datatypes }

let app name arguments = "(" ^ String.concat " " (name :: arguments) ^ ")"
let and_ terms = match terms with [] -> "true" | [ term ] -> term | _ -> app "and" terms
let or_ terms = match terms with [] -> "false" | [ term ] -> term | _ -> app "or" terms

let selector constructor index = Printf.sprintf "sel_%s_%d" constructor.smt_name index
let recognizer constructor = "is_" ^ constructor.smt_name

let lookup ~loc env name =
  match List.assoc_opt name env with
  | Some value -> value
  | None -> error ~loc "unknown logical variable or unsupported global `%s`" name

let rec smt_of_pattern registry env scrutinee pattern =
  match pattern.ppat_desc with
  | Ppat_any -> ("true", env)
  | Ppat_var { txt = name; _ } -> ("true", (name, scrutinee) :: env)
  | Ppat_constraint (inner, _) -> smt_of_pattern registry env scrutinee inner
  | Ppat_constant { pconst_desc = Pconst_integer (value, _); _ } ->
      (app "=" [ scrutinee; value ], env)
  | Ppat_construct ({ txt = Lident "true"; _ }, None) ->
      (app "=" [ scrutinee; "true" ], env)
  | Ppat_construct ({ txt = Lident "false"; _ }, None) ->
      (app "=" [ scrutinee; "false" ], env)
  | Ppat_construct ({ txt; _ }, argument) ->
      let name = longident_last txt in
      let constructor =
        match Hashtbl.find_opt registry.constructors name with
        | Some constructor -> constructor
        | None -> error ~loc:pattern.ppat_loc "unknown constructor `%s`" name
      in
      let patterns =
        match argument with None -> [] | Some (_, pattern) -> flatten_pattern pattern
      in
      if List.length patterns <> List.length constructor.arguments then
        error ~loc:pattern.ppat_loc "constructor `%s` has the wrong arity" name;
      let guard, env =
        List.fold_left2
          (fun (guards, env) index pattern ->
            let guard, env =
              smt_of_pattern registry env (app (selector constructor index) [ scrutinee ])
                pattern
            in
            (guard :: guards, env))
          ([], env)
          (List.init (List.length patterns) Fun.id)
          patterns
      in
      (and_ (app (recognizer constructor) [ scrutinee ] :: guard), env)
  | _ -> error ~loc:pattern.ppat_loc "this pattern is not yet supported by the SMT core"

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

let rec smt_of_expression registry env expression =
  let recurse = smt_of_expression registry env in
  match expression.pexp_desc with
  | Pexp_ident { txt; _ } -> lookup ~loc:expression.pexp_loc env (longident_last txt)
  | Pexp_constant { pconst_desc = Pconst_integer (value, _); _ } -> value
  | Pexp_construct ({ txt = Lident "true"; _ }, None) -> "true"
  | Pexp_construct ({ txt = Lident "false"; _ }, None) -> "false"
  | Pexp_construct ({ txt; _ }, argument) ->
      let name = longident_last txt in
      let constructor =
        match Hashtbl.find_opt registry.constructors name with
        | Some constructor -> constructor
        | None -> error ~loc:expression.pexp_loc "unknown constructor `%s`" name
      in
      let arguments =
        match argument with
        | None -> []
        | Some { pexp_desc = Pexp_tuple expressions; _ } ->
            List.map recurse expressions
        | Some expression -> [ recurse expression ]
      in
      if List.length arguments <> List.length constructor.arguments then
        error ~loc:expression.pexp_loc "constructor `%s` has the wrong arity" name;
      if arguments = [] then constructor.smt_name else app constructor.smt_name arguments
  | Pexp_apply
      ({ pexp_desc = Pexp_ident { txt; _ }; _ },
       [ (Nolabel, left); (Nolabel, right) ]) -> (
      let name = longident_last txt in
      match binary_operator name with
      | Some operator -> app operator [ recurse left; recurse right ]
      | None ->
          error ~loc:expression.pexp_loc
            "call to `%s` needs a summary; interprocedural checking is planned" name)
  | Pexp_apply
      ({ pexp_desc = Pexp_ident { txt = Lident "not"; _ }; _ },
       [ (Nolabel, argument) ]) -> app "not" [ recurse argument ]
  | Pexp_apply
      ({ pexp_desc = Pexp_ident { txt = Lident ("~-" | "-"); _ }; _ },
       [ (Nolabel, argument) ]) -> app "-" [ recurse argument ]
  | Pexp_ifthenelse (condition, if_true, Some if_false) ->
      app "ite" [ recurse condition; recurse if_true; recurse if_false ]
  | Pexp_let (Nonrecursive, [ binding ], body) -> (
      match binding.pvb_pat.ppat_desc with
      | Ppat_var { txt = name; _ } ->
          let value = recurse binding.pvb_expr in
          smt_of_expression registry ((name, value) :: env) body
      | _ ->
          error ~loc:binding.pvb_loc
            "local refinement lets currently require a variable pattern")
  | Pexp_constraint (inner, _) -> recurse inner
  | Pexp_match (scrutinee, cases) ->
      if List.exists (fun case -> Option.is_some case.pc_guard) cases then
        error ~loc:expression.pexp_loc
          "guarded matches require an explicit fall-through semantics";
      let catch_all pattern =
        match pattern.ppat_desc with
        | Ppat_any | Ppat_var _ -> true
        | Ppat_constraint (inner, _) -> (
            match inner.ppat_desc with Ppat_any | Ppat_var _ -> true | _ -> false)
        | _ -> false
      in
      let constructor_name pattern =
        let pattern =
          match pattern.ppat_desc with Ppat_constraint (inner, _) -> inner | _ -> pattern
        in
        match pattern.ppat_desc with
        | Ppat_construct ({ txt; _ }, _) -> Some (longident_last txt)
        | _ -> None
      in
      let exhaustive =
        List.exists (fun case -> catch_all case.pc_lhs) cases
        ||
        let names = List.filter_map (fun case -> constructor_name case.pc_lhs) cases in
        List.length names = List.length cases
        && List.exists
             (fun (datatype : datatype) ->
               List.length datatype.constructors = List.length names
               && List.for_all
                    (fun constructor ->
                      List.exists
                        (fun name ->
                          match Hashtbl.find_opt registry.constructors name with
                          | Some found -> found.smt_name = constructor.smt_name
                          | None -> false)
                        names)
                    datatype.constructors)
             registry.datatypes
      in
      if not exhaustive then
        error ~loc:expression.pexp_loc
          "match is not visibly exhaustive; add a catch-all or cover one declared ADT";
      let scrutinee = recurse scrutinee in
      let translate_case case =
        let guard, case_env = smt_of_pattern registry env scrutinee case.pc_lhs in
        let guard =
          match case.pc_guard with
          | None -> guard
          | Some extra ->
              and_ [ guard; smt_of_expression registry case_env extra ]
        in
        (guard, smt_of_expression registry case_env case.pc_rhs)
      in
      let cases = List.map translate_case cases in
      let rec decision_tree = function
        | [] -> error ~loc:expression.pexp_loc "empty match"
        | [ (_, body) ] -> body
        | (guard, body) :: rest -> app "ite" [ guard; body; decision_tree rest ]
      in
      decision_tree cases
  | Pexp_field (record, { txt; _ }) ->
      let field = longident_last txt in
      let constructor, index =
        match Hashtbl.find_opt registry.fields field with
        | Some entry -> entry
        | None -> error ~loc:expression.pexp_loc "unknown record field `%s`" field
      in
      app (selector constructor index) [ recurse record ]
  | Pexp_record (fields, None) ->
      let entries =
        List.map
          (fun ({ txt; _ }, value) ->
            let field = longident_last txt in
            match Hashtbl.find_opt registry.fields field with
            | Some (constructor, index) -> (constructor, index, recurse value)
            | None -> error ~loc:value.pexp_loc "unknown record field `%s`" field)
          fields
      in
      let constructor =
        match entries with
        | (constructor, _, _) :: _ -> constructor
        | [] -> error ~loc:expression.pexp_loc "empty records are not supported"
      in
      let values =
        List.init (List.length constructor.arguments) (fun index ->
            match List.find_opt (fun (_, current, _) -> current = index) entries with
            | Some (_, _, value) -> value
            | None -> error ~loc:expression.pexp_loc "record literal is missing a field")
      in
      app constructor.smt_name values
  | _ ->
      error ~loc:expression.pexp_loc
        "unsupported expression in refinement core (effects and higher-order values need an explicit theory)"

let parse_formula ~filename ~loc text =
  let lexbuf = Lexing.from_string text in
  Location.init lexbuf filename;
  try Parse.expression lexbuf
  with _ -> error ~loc "cannot parse refinement formula `%s`" text

let binder (name, sort) = Printf.sprintf "(%s %s)" (smt_identifier name) (smt_sort sort)

let datatype_prelude registry extra_sorts =
  let buffer = Buffer.create 4096 in
  let line format = Printf.kbprintf (fun _ -> Buffer.add_char buffer '\n') buffer format in
  line "; User datatypes are deliberately uninterpreted sorts plus axioms.";
  let datatype_sorts =
    List.concat_map
      (fun (datatype : datatype) ->
        List.concat_map (fun constructor -> constructor.arguments) datatype.constructors)
      registry.datatypes
  in
  if List.exists (( = ) Unit) (extra_sorts @ datatype_sorts) then (
    line "(declare-sort Unit 0)";
    line "(declare-fun unit () Unit)");
  List.iter
    (fun (datatype : datatype) ->
      line "(declare-sort %s 0)" (smt_sort (User datatype.type_name)))
    registry.datatypes;
  List.iter
    (fun (datatype : datatype) ->
      let result_sort = smt_sort (User datatype.type_name) in
      List.iter
        (fun constructor ->
          line "(declare-fun %s (%s) %s)" constructor.smt_name
            (String.concat " " (List.map smt_sort constructor.arguments))
            result_sort;
          line "(declare-fun %s (%s) Bool)" (recognizer constructor) result_sort;
          List.iteri
            (fun index sort ->
              line "(declare-fun %s (%s) %s)" (selector constructor index)
                result_sort (smt_sort sort))
            constructor.arguments)
        datatype.constructors)
    registry.datatypes;
  List.iter
    (fun (datatype : datatype) ->
      let result_sort = smt_sort (User datatype.type_name) in
      List.iter
        (fun constructor ->
          let arguments =
            List.mapi (fun index sort -> ("a" ^ string_of_int index, sort))
              constructor.arguments
          in
          let terms = List.map fst arguments in
          let constructed =
            if terms = [] then constructor.smt_name else app constructor.smt_name terms
          in
          let quantified formula =
            if arguments = [] then formula
            else app "forall" [ "(" ^ String.concat " " (List.map binder arguments) ^ ")"; formula ]
          in
          line "(assert %s)" (quantified (app (recognizer constructor) [ constructed ]));
          List.iteri
            (fun index _ ->
              line "(assert %s)"
                (quantified
                   (app "=" [ app (selector constructor index) [ constructed ]; List.nth terms index ])))
            constructor.arguments;
          List.iter
            (fun other ->
              if other.smt_name <> constructor.smt_name then
                line "(assert %s)"
                  (quantified (app "not" [ app (recognizer other) [ constructed ] ])))
            datatype.constructors)
        datatype.constructors;
      let value = "v" in
      line "(assert (forall ((%s %s)) %s))" value result_sort
        (or_
           (List.map
              (fun constructor -> app (recognizer constructor) [ value ])
              datatype.constructors));
      List.iter
        (fun constructor ->
          let rebuilt =
            let fields =
              List.mapi
                (fun index _ -> app (selector constructor index) [ value ])
                constructor.arguments
            in
            if fields = [] then constructor.smt_name else app constructor.smt_name fields
          in
          line "(assert (forall ((%s %s)) (=> (%s %s) (= %s %s))))" value
            result_sort (recognizer constructor) value value rebuilt)
        datatype.constructors)
    registry.datatypes;
  Buffer.contents buffer

let smt_for_contract registry ~filename mode arguments result_sort body pre post =
  let env = List.map (fun (name, _) -> (name, smt_identifier name)) arguments in
  let body = smt_of_expression registry env body in
  let pre = smt_of_expression registry env (parse_formula ~filename ~loc:Location.none pre) in
  let post_expression = parse_formula ~filename ~loc:Location.none post in
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer "(set-option :produce-models true)\n(set-logic ALL)\n";
  Buffer.add_string buffer
    (datatype_prelude registry (result_sort :: List.map snd arguments));
  (match mode with
  | Over ->
      let post =
        smt_of_expression registry (("result", "result") :: env) post_expression
      in
      List.iter
        (fun (name, sort) ->
          Buffer.add_string buffer
            (Printf.sprintf "(declare-const %s %s)\n" (smt_identifier name)
               (smt_sort sort)))
        arguments;
      Buffer.add_string buffer (Printf.sprintf "(assert %s)\n" pre);
      Buffer.add_string buffer
        (Printf.sprintf "(assert (not (let ((result %s)) %s)))\n" body post)
  | Under ->
      let missing_result = "missing_result" in
      let post =
        smt_of_expression registry [ ("result", missing_result) ] post_expression
      in
      let input_binders =
        "(" ^ String.concat " " (List.map binder arguments) ^ ")"
      in
      let witness = and_ [ pre; app "=" [ missing_result; body ] ] in
      Buffer.add_string buffer
        (Printf.sprintf "(declare-const %s %s)\n" missing_result (smt_sort result_sort));
      Buffer.add_string buffer (Printf.sprintf "(assert %s)\n" post);
      Buffer.add_string buffer
        (Printf.sprintf "(assert (forall %s (not %s)))\n" input_binders witness));
  Buffer.add_string buffer "(check-sat)\n(get-model)\n";
  Buffer.contents buffer

let obligations_of_file filename =
  let channel = open_in filename in
  let lexbuf = Lexing.from_channel channel in
  Location.init lexbuf filename;
  let structure =
    Fun.protect ~finally:(fun () -> close_in channel) (fun () -> Parse.implementation lexbuf)
  in
  let registry = register_types structure in
  List.concat_map
    (fun item ->
      match item.pstr_desc with
      | Pstr_value (_, bindings) ->
          List.filter_map
            (fun binding ->
              match contract_of_attributes binding.pvb_attributes with
              | None -> None
              | Some (mode, pre, post) ->
                  let name =
                    match binding.pvb_pat.ppat_desc with
                    | Ppat_var { txt; _ } -> txt
                    | _ ->
                        error ~loc:binding.pvb_pat.ppat_loc
                          "a refined top-level binding must have a simple name"
                  in
                  let arguments, result_sort, body = function_shape binding.pvb_expr in
                  Some
                    {
                      name;
                      mode;
                      location = binding.pvb_loc;
                      smt =
                        smt_for_contract registry ~filename mode arguments result_sort body
                          pre post;
                    })
            bindings
      | _ -> [])
    structure

let read_all channel =
  let buffer = Buffer.create 1024 in
  (try
     while true do
       Buffer.add_string buffer (input_line channel);
       Buffer.add_char buffer '\n'
     done
   with End_of_file -> ());
  Buffer.contents buffer

let solve obligation =
  let input, output, error = Unix.open_process_full "z3 -in" (Unix.environment ()) in
  output_string output obligation.smt;
  close_out output;
  let stdout = read_all input in
  let stderr = read_all error in
  ignore (Unix.close_process_full (input, output, error));
  let first_line =
    match String.split_on_char '\n' stdout with line :: _ -> String.trim line | [] -> ""
  in
  match first_line with
  | "unsat" -> Valid
  | "sat" -> Invalid stdout
  | "unknown" -> Unknown (stdout ^ stderr)
  | _ -> Unknown (stdout ^ stderr)
