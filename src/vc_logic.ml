open Refined_ir
open Refined_types
open Refined_common
open Parsetree
open Asttypes

module Sort_term = struct
  type t = Typed_core.sort

  type head =
    | Integer
    | Boolean
    | Unit
    | Tuple
    | Application of Typed_core.symbol

  let view = function
    | Typed_core.S_var variable -> `Variable variable
    | S_int -> `Node (Integer, [])
    | S_bool -> `Node (Boolean, [])
    | S_unit -> `Node (Unit, [])
    | S_tuple elements -> `Node (Tuple, elements)
    | S_app (symbol, arguments) -> `Node (Application symbol, arguments)

  let make_node head children =
    match (head, children) with
    | Integer, [] -> Typed_core.S_int
    | Boolean, [] -> S_bool
    | Unit, [] -> S_unit
    | Tuple, elements -> S_tuple elements
    | Application symbol, arguments -> S_app (symbol, arguments)
    | (Integer | Boolean | Unit), _ -> invalid_arg "base sort with arguments"

  let equal_head left right =
    match (left, right) with
    | Integer, Integer | Boolean, Boolean | Unit, Unit | Tuple, Tuple -> true
    | Application left, Application right -> left.key = right.key
    | _ -> false

  let equal = ( = )
end

module Sort_evars = Evar_context.Make (Sort_term)

let typed_smt_sort =
  let rec translate = function
    | Typed_core.S_int -> "Int"
    | S_bool -> "Bool"
    | S_unit -> "Unit"
    | S_var name -> "Tvar_" ^ smt_identifier name
    | S_tuple elements ->
        "Tuple_"
        ^ String.concat "_"
            (List.map (fun sort -> smt_identifier (translate sort)) elements)
    | S_app (symbol, arguments) ->
        let suffix =
          match arguments with
          | [] -> ""
          | _ ->
              "_"
              ^ String.concat "_"
                  (List.map
                     (fun sort -> smt_identifier (translate sort))
                     arguments)
        in
        "T_" ^ smt_identifier symbol.key ^ suffix
  in
  translate

let reference_content_sort = function
  | Typed_core.S_app (symbol, [ content ])
    when symbol.display = "ref" || symbol.key = "ref"
         || String.ends_with ~suffix:".ref" symbol.key ->
      Some content
  | _ -> None

let typed_constructor_name (constructor : Typed_core.constructor) =
  "C_"
  ^ smt_identifier constructor.Typed_core.symbol.key
  ^ "__"
  ^ smt_identifier (typed_smt_sort constructor.result)

let typed_recognizer (constructor : Typed_core.constructor) =
  "is_" ^ typed_constructor_name constructor

let typed_selector (constructor : Typed_core.constructor) index =
  Printf.sprintf "sel_%s_%d" (typed_constructor_name constructor) index

let typed_tuple_constructor sort = "mk_" ^ typed_smt_sort sort

let typed_tuple_selector sort index =
  Printf.sprintf "sel_%s_%d" (typed_smt_sort sort) index

let typed_logic_name (logic_symbol : Typed_core.logic_symbol) =
  "L_" ^ smt_identifier logic_symbol.logic_name.key

let typed_lookup_logic registry scope name =
  let rec candidates scope =
    match scope with
    | [] -> [ name ]
    | _ ->
        qualified_name scope name
        :: candidates (List.rev (List.tl (List.rev scope)))
  in
  let names = candidates scope in
  let rec expand_alias visited name =
    if List.mem name visited then name
    else
      let parts = String.split_on_char '.' name in
      let rec longest length =
        if length = 0 then None
        else
          let prefix =
            parts |> List.to_seq |> Seq.take length |> List.of_seq
            |> String.concat "."
          in
          match Hashtbl.find_opt registry.Typed_core.module_aliases prefix with
          | Some target ->
              let suffix =
                parts |> List.to_seq |> Seq.drop length |> List.of_seq
              in
              Some (String.concat "." (target :: suffix))
          | None -> longest (length - 1)
      in
      match longest (List.length parts - 1) with
      | None -> name
      | Some expanded -> expand_alias (name :: visited) expanded
  in
  List.find_map
    (fun candidate ->
      let expanded = expand_alias [] candidate in
      match Hashtbl.find_opt registry.Typed_core.logic_by_name expanded with
      | Some symbol -> Some symbol
      | None -> Hashtbl.find_opt registry.logic_by_name candidate)
    names

let typed_specialize_program (program : Typed_core.program)
    (function_def : Typed_core.function_def) pre_expression post_expression =
  let open Typed_core in
  let substitutions = Sort_evars.create () in
  let substitute = Sort_evars.substitute substitutions in
  let unify ~loc formal actual =
    match Sort_evars.unify substitutions ~formal ~actual with
    | Ok () -> ()
    | Error (Occurs (variable, actual)) ->
        typed_error ~loc "cyclic instantiation for `%s` in %s" variable
          (typed_smt_sort actual)
    | Error (Shape_mismatch (formal, actual)) ->
        typed_error ~loc
          "logical predicate type mismatch: expected %s but got %s"
          (typed_smt_sort formal) (typed_smt_sort actual)
  in
  let formula_env =
    List.map
      (fun (symbol, sort) -> (symbol.Typed_core.display, sort))
      function_def.arguments
  in
  let rec infer_formula scope env expression =
    let recurse = infer_formula scope env in
    match expression.Parsetree.pexp_desc with
    | Pexp_ident { txt; _ } -> (
        let name = longident_name txt in
        match List.assoc_opt name env with
        | Some sort -> sort
        | None ->
            typed_error ~loc:expression.pexp_loc "unknown logical variable `%s`"
              name)
    | Pexp_constant { pconst_desc = Pconst_integer _; _ } -> Typed_core.S_int
    | Pexp_construct ({ txt = Lident ("true" | "false"); _ }, None) -> S_bool
    | Pexp_construct ({ txt; _ }, _) -> (
        let name = longident_last txt in
        match Hashtbl.find_opt program.registry.constructors_by_name name with
        | Some constructor -> (
            match
              List.find_opt
                (fun (datatype : Typed_core.datatype) ->
                  List.exists
                    (fun (candidate : Typed_core.constructor) ->
                      candidate.symbol.key = constructor.Typed_core.symbol.key)
                    datatype.constructors)
                program.registry.datatype_templates
            with
            | Some datatype -> datatype.owner
            | None ->
                typed_error ~loc:expression.pexp_loc
                  "constructor `%s` has no registered owner" name)
        | None ->
            typed_error ~loc:expression.pexp_loc "unknown constructor `%s`" name
        )
    | Pexp_apply
        ( { pexp_desc = Pexp_ident { txt = Lident "not"; _ }; _ },
          [ (Nolabel, argument) ] ) ->
        unify ~loc:expression.pexp_loc S_bool (recurse argument);
        S_bool
    | Pexp_apply ({ pexp_desc = Pexp_ident { txt; _ }; _ }, arguments) -> (
        let name = longident_name txt in
        let argument_sorts =
          List.map
            (function
              | Nolabel, argument -> recurse argument
              | _ ->
                  typed_error ~loc:expression.pexp_loc
                    "logical applications cannot use labels")
            arguments
        in
        match binary_operator name with
        | Some ("+" | "-" | "*" | "div" | "mod") ->
            List.iter (unify ~loc:expression.pexp_loc S_int) argument_sorts;
            S_int
        | Some ("=" | "distinct") -> S_bool
        | Some _ -> S_bool
        | None -> (
            match typed_lookup_logic program.registry scope name with
            | Some logic_symbol ->
                if
                  List.length argument_sorts
                  <> List.length logic_symbol.arguments
                then
                  typed_error ~loc:expression.pexp_loc
                    "logical predicate `%s` expects %d arguments" name
                    (List.length logic_symbol.arguments);
                List.iter2
                  (unify ~loc:expression.pexp_loc)
                  logic_symbol.arguments argument_sorts;
                substitute logic_symbol.result
            | None ->
                typed_error ~loc:expression.pexp_loc
                  "unknown logical predicate `%s`" name))
    | Pexp_field (record, { txt; _ }) -> (
        ignore (recurse record);
        let name = longident_last txt in
        match Hashtbl.find_opt program.registry.fields_by_name name with
        | Some (constructor, index) ->
            List.nth constructor.Typed_core.arguments index
        | None ->
            typed_error ~loc:expression.pexp_loc "unknown record field `%s`"
              name)
    | _ -> typed_error ~loc:expression.pexp_loc "unsupported refinement formula"
  in
  let rec infer_core expression =
    let recurse = infer_core in
    match expression.Typed_core.desc with
    | Apply (symbol, arguments) ->
        List.iter recurse arguments;
        Option.iter
          (fun (logic_symbol : Typed_core.logic_symbol) ->
            if
              List.length arguments
              <> List.length logic_symbol.Typed_core.arguments
            then
              typed_error_at expression.loc
                "logical predicate `%s` has an unsupported application arity"
                symbol.display;
            List.iter2
              (fun formal (actual : Typed_core.expr) ->
                unify
                  ~loc:(location_of_span actual.Typed_core.loc)
                  formal actual.sort)
              logic_symbol.arguments arguments)
          (typed_lookup_logic program.registry [] symbol.key)
    | Tuple expressions | Choose expressions -> List.iter recurse expressions
    | Construct (_, expressions) | Record (_, expressions) ->
        List.iter recurse expressions
    | If (condition, if_true, if_false) ->
        List.iter recurse [ condition; if_true; if_false ]
    | Let (_, value, body) ->
        recurse value;
        recurse body
    | Match (scrutinee, cases) ->
        recurse scrutinee;
        List.iter (fun (_, body) -> recurse body) cases
    | Field (_, _, record) -> recurse record
    | Var _ | Int _ | Bool _ | Raise (_, None) | Perform (_, None) | Deref _ ->
        ()
    | Raise (_, Some payload) | Perform (_, Some payload) -> recurse payload
    | Ref (_, initial) -> recurse initial
    | Try (body, cases) ->
        recurse body;
        List.iter (fun (_, handler) -> recurse handler) cases
    | Let_ref (_, _, initial, body) ->
        recurse initial;
        recurse body
    | Assign (_, value) -> recurse value
    | Sequence (first, second) ->
        recurse first;
        recurse second
    | Handle (body, handlers) ->
        recurse body;
        let rec recurse_action = function
          | Typed_core.Abort handler | Typed_core.Resume handler ->
              recurse handler
          | Typed_core.Conditional (condition, if_true, if_false) ->
              recurse condition;
              recurse_action if_true;
              recurse_action if_false
        in
        List.iter (fun (_, _, action) -> recurse_action action) handlers
  in
  ignore (infer_formula [] formula_env pre_expression);
  ignore
    (infer_formula []
       (("result", function_def.result) :: formula_env)
       post_expression);
  infer_core function_def.body;
  if not (Sort_evars.has_solutions substitutions) then program
  else
    let logic_by_name =
      Hashtbl.create (Hashtbl.length program.registry.logic_by_name)
    in
    Hashtbl.iter
      (fun name (logic_symbol : Typed_core.logic_symbol) ->
        let arguments = List.map substitute logic_symbol.arguments in
        let result = substitute logic_symbol.result in
        let suffix =
          String.concat "_"
            (List.map
               (fun sort -> smt_identifier (typed_smt_sort sort))
               arguments)
        in
        let logic_name =
          {
            logic_symbol.logic_name with
            key = logic_symbol.logic_name.key ^ ".instance." ^ suffix;
          }
        in
        Hashtbl.replace logic_by_name name { logic_name; arguments; result })
      program.registry.logic_by_name;
    let specialize_statements statements =
      List.map
        (fun (axiom : Typed_core.axiom) ->
          {
            axiom with
            variables =
              List.map
                (fun (name, sort) -> (name, substitute sort))
                axiom.variables;
          })
        statements
    in
    let axioms = specialize_statements program.registry.axioms in
    let checked_lemmas =
      specialize_statements program.registry.checked_lemmas
    in
    let registry =
      { program.registry with logic_by_name; axioms; checked_lemmas }
    in
    { program with registry }

let typed_monomorphize_datatypes (program : Typed_core.program)
    (function_def : Typed_core.function_def) =
  let templates = program.registry.Typed_core.datatype_templates in
  let template_for = function
    | Typed_core.S_app (symbol, _) ->
        List.find_opt
          (fun (datatype : Typed_core.datatype) ->
            match datatype.owner with
            | S_app (owner, _) -> owner.key = symbol.key
            | _ -> false)
          templates
    | _ -> None
  in
  let rec closed = function
    | Typed_core.S_var _ -> false
    | S_tuple sorts | S_app (_, sorts) -> List.for_all closed sorts
    | S_int | S_bool | S_unit -> true
  in
  let instances = Hashtbl.create 16 in
  let open_instance = ref None in
  let rec collect sort =
    (match template_for sort with
    | Some _ when closed sort ->
        Hashtbl.replace instances (typed_smt_sort sort) sort
    | Some _ -> open_instance := Some sort
    | None -> ());
    match sort with
    | Typed_core.S_tuple sorts | S_app (_, sorts) -> List.iter collect sorts
    | S_int | S_bool | S_unit | S_var _ -> ()
  in
  let rec collect_pattern = function
    | Typed_core.Pat_construct (constructor, patterns) ->
        collect constructor.result;
        List.iter collect constructor.arguments;
        List.iter collect_pattern patterns
    | Pat_tuple (sort, patterns) ->
        collect sort;
        List.iter collect_pattern patterns
    | Pat_alias (pattern, _) -> collect_pattern pattern
    | Pat_any | Pat_var _ | Pat_int _ | Pat_bool _ -> ()
  in
  let rec collect_expression (expression : Typed_core.expr) =
    collect expression.sort;
    match expression.desc with
    | Var _ | Int _ | Bool _ | Raise (_, None) | Perform (_, None) | Deref _ ->
        ()
    | Raise (_, Some payload) | Perform (_, Some payload) ->
        collect_expression payload
    | Ref (sort, initial) ->
        collect sort;
        collect_expression initial
    | Construct (constructor, expressions) | Record (constructor, expressions)
      ->
        collect constructor.result;
        List.iter collect constructor.arguments;
        List.iter collect_expression expressions
    | Tuple expressions | Choose expressions | Apply (_, expressions) ->
        List.iter collect_expression expressions
    | If (condition, if_true, if_false) ->
        List.iter collect_expression [ condition; if_true; if_false ]
    | Let (_, value, body) -> List.iter collect_expression [ value; body ]
    | Match (scrutinee, cases) ->
        collect_expression scrutinee;
        List.iter
          (fun (pattern, body) ->
            collect_pattern pattern;
            collect_expression body)
          cases
    | Field (constructor, _, record) ->
        collect constructor.result;
        List.iter collect constructor.arguments;
        collect_expression record
    | Try (body, cases) ->
        collect_expression body;
        List.iter (fun (_, handler) -> collect_expression handler) cases
    | Let_ref (_, sort, initial, body) ->
        collect sort;
        collect_expression initial;
        collect_expression body
    | Assign (_, value) -> collect_expression value
    | Sequence (first, second) ->
        collect_expression first;
        collect_expression second
    | Handle (body, handlers) ->
        collect_expression body;
        let rec collect_action = function
          | Typed_core.Abort handler | Typed_core.Resume handler ->
              collect_expression handler
          | Typed_core.Conditional (condition, if_true, if_false) ->
              collect_expression condition;
              collect_action if_true;
              collect_action if_false
        in
        List.iter (fun (_, _, action) -> collect_action action) handlers
  in
  List.iter (fun (_, sort) -> collect sort) function_def.arguments;
  collect function_def.result;
  List.iter
    (fun (contract : Typed_core.contract) ->
      List.iter (fun (_, sort) -> collect sort) contract.ghosts)
    function_def.contracts;
  collect_expression function_def.body;
  (match !open_instance with
  | Some sort ->
      typed_error_at function_def.body.loc
        "parameterized ADT `%s` has no finite closed use-site instance"
        (typed_smt_sort sort)
  | None -> ());
  let instantiate (template : Typed_core.datatype) concrete =
    let substitutions = Sort_evars.create () in
    (match
       Sort_evars.unify substitutions ~formal:template.owner ~actual:concrete
     with
    | Ok () -> ()
    | Error _ -> assert false);
    let substitute = Sort_evars.substitute substitutions in
    {
      Typed_core.owner = concrete;
      constructors =
        List.map
          (fun (constructor : Typed_core.constructor) ->
            {
              constructor with
              arguments = List.map substitute constructor.arguments;
              result = substitute constructor.result;
            })
          template.constructors;
    }
  in
  let datatypes =
    Hashtbl.fold
      (fun _ concrete result ->
        match template_for concrete with
        | Some template -> instantiate template concrete :: result
        | None -> result)
      instances []
    |> List.sort (fun left right ->
        String.compare
          (typed_smt_sort left.Typed_core.owner)
          (typed_smt_sort right.Typed_core.owner))
  in
  let constructors_by_name = Hashtbl.create 32 in
  let constructors_by_uid = Hashtbl.create 32 in
  let constructor_candidates symbol_key =
    List.concat_map
      (fun (datatype : Typed_core.datatype) ->
        List.filter
          (fun (constructor : Typed_core.constructor) ->
            constructor.symbol.key = symbol_key)
          datatype.constructors)
      datatypes
  in
  Hashtbl.iter
    (fun name (template : Typed_core.constructor) ->
      match constructor_candidates template.symbol.key with
      | [ constructor ] -> Hashtbl.replace constructors_by_name name constructor
      | _ -> ())
    program.registry.constructors_by_name;
  Hashtbl.iter
    (fun uid (template : Typed_core.constructor) ->
      match constructor_candidates template.symbol.key with
      | [ constructor ] -> Hashtbl.replace constructors_by_uid uid constructor
      | _ -> ())
    program.registry.constructors_by_uid;
  let fields_by_name = Hashtbl.create 32 in
  let fields_by_uid = Hashtbl.create 32 in
  let specialize_field table key ((template : Typed_core.constructor), index) =
    match constructor_candidates template.Typed_core.symbol.key with
    | [ constructor ] -> Hashtbl.replace table key (constructor, index)
    | _ -> Hashtbl.replace table key (template, index)
  in
  Hashtbl.iter (specialize_field fields_by_name) program.registry.fields_by_name;
  Hashtbl.iter (specialize_field fields_by_uid) program.registry.fields_by_uid;
  let registry =
    {
      program.registry with
      constructors_by_uid;
      constructors_by_name;
      fields_by_uid;
      fields_by_name;
      datatypes;
    }
  in
  { program with registry }

exception Logic_needs_expected of Location.t * string

let elaborate_formula ?(scope = []) ?(expected = Typed_core.S_bool) registry env
    expression =
  let open Logic_term in
  let ensure_sort ~loc expected actual =
    if expected <> actual then
      typed_error ~loc "logical sort mismatch: expected %s but got %s"
        (typed_smt_sort expected) (typed_smt_sort actual)
  in
  let finish ?expected ~loc term =
    Option.iter (fun expected -> ensure_sort ~loc expected term.sort) expected;
    term
  in
  let constructors_named name =
    List.concat_map
      (fun (datatype : Typed_core.datatype) ->
        List.filter
          (fun (constructor : Typed_core.constructor) ->
            constructor.symbol.display = name)
          datatype.constructors)
      registry.Typed_core.datatypes
  in
  let constructor_arguments argument =
    match argument with
    | None -> []
    | Some { Parsetree.pexp_desc = Pexp_tuple expressions; pexp_loc; _ } ->
        List.map
          (function
            | None, expression -> expression
            | Some _, _ ->
                typed_error ~loc:pexp_loc
                  "labelled tuple constructor arguments are not supported")
          expressions
    | Some expression -> [ expression ]
  in
  let rec elaborate ?expected expression =
    let loc = expression.Parsetree.pexp_loc in
    match expression.pexp_desc with
    | Pexp_ident { txt; _ } -> (
        let name = longident_name txt in
        match List.assoc_opt name env with
        | Some (variable, sort) ->
            finish ?expected ~loc { desc = Variable variable; sort }
        | None -> (
            match typed_lookup_logic registry scope name with
            | Some logic_symbol when logic_symbol.arguments = [] ->
                finish ?expected ~loc
                  {
                    desc = Application (Logic logic_symbol, []);
                    sort = logic_symbol.result;
                  }
            | _ -> typed_error ~loc "unknown logical variable `%s`" name))
    | Pexp_constant { pconst_desc = Pconst_integer (value, _); _ } ->
        finish ?expected ~loc
          { desc = Integer (int_of_string value); sort = Typed_core.S_int }
    | Pexp_construct ({ txt = Lident "true"; _ }, None) ->
        finish ?expected ~loc { desc = Boolean true; sort = Typed_core.S_bool }
    | Pexp_construct ({ txt = Lident "false"; _ }, None) ->
        finish ?expected ~loc { desc = Boolean false; sort = Typed_core.S_bool }
    | Pexp_construct ({ txt; _ }, argument) ->
        let name = longident_last txt in
        let expressions = constructor_arguments argument in
        let candidates =
          constructors_named name
          |> List.filter (fun (constructor : Typed_core.constructor) ->
              List.length constructor.Typed_core.arguments
              = List.length expressions)
          |> List.filter (fun (constructor : Typed_core.constructor) ->
              match expected with
              | Some expected -> constructor.result = expected
              | None -> true)
        in
        let candidates =
          match (expected, candidates) with
          | Some _, _ | None, [] | None, [ _ ] -> candidates
          | None, candidates ->
              let inferred = List.map elaborate expressions in
              List.filter
                (fun (constructor : Typed_core.constructor) ->
                  List.map (fun term -> term.sort) inferred
                  = constructor.Typed_core.arguments)
                candidates
        in
        let constructor =
          match candidates with
          | [ constructor ] -> constructor
          | [] ->
              typed_error ~loc "constructor `%s` has no matching logic sort"
                name
          | _ ->
              raise (Logic_needs_expected (loc, "constructor `" ^ name ^ "`"))
        in
        let arguments =
          List.map2
            (fun expected expression -> elaborate ~expected expression)
            constructor.arguments expressions
        in
        finish ?expected ~loc
          {
            desc = Application (Constructor constructor, arguments);
            sort = constructor.result;
          }
    | Pexp_apply
        ( { pexp_desc = Pexp_ident { txt = Lident "not"; _ }; _ },
          [ (Nolabel, argument) ] ) ->
        let argument = elaborate ~expected:Typed_core.S_bool argument in
        finish ?expected ~loc
          {
            desc = Application (Builtin "not", [ argument ]);
            sort = Typed_core.S_bool;
          }
    | Pexp_apply ({ pexp_desc = Pexp_ident { txt; _ }; _ }, arguments) -> (
        let name = longident_name txt in
        let arguments =
          List.map
            (function
              | Nolabel, argument -> argument
              | _ -> typed_error ~loc "logical applications cannot use labels")
            arguments
        in
        match (binary_operator name, arguments) with
        | Some (("=" | "distinct") as operator), [ left; right ] ->
            let left, right =
              try
                let left = elaborate left in
                (left, elaborate ~expected:left.sort right)
              with Logic_needs_expected _ ->
                let right = elaborate right in
                (elaborate ~expected:right.sort left, right)
            in
            finish ?expected ~loc
              {
                desc = Application (Builtin operator, [ left; right ]);
                sort = Typed_core.S_bool;
              }
        | Some (("+" | "-" | "*" | "div" | "mod") as operator), [ left; right ]
          ->
            let left = elaborate ~expected:Typed_core.S_int left in
            let right = elaborate ~expected:Typed_core.S_int right in
            finish ?expected ~loc
              {
                desc = Application (Builtin operator, [ left; right ]);
                sort = Typed_core.S_int;
              }
        | Some (("<" | "<=" | ">" | ">=") as operator), [ left; right ] ->
            let left = elaborate ~expected:Typed_core.S_int left in
            let right = elaborate ~expected:Typed_core.S_int right in
            finish ?expected ~loc
              {
                desc = Application (Builtin operator, [ left; right ]);
                sort = Typed_core.S_bool;
              }
        | Some (("and" | "or" | "=>") as operator), [ left; right ] ->
            let left = elaborate ~expected:Typed_core.S_bool left in
            let right = elaborate ~expected:Typed_core.S_bool right in
            finish ?expected ~loc
              {
                desc = Application (Builtin operator, [ left; right ]);
                sort = Typed_core.S_bool;
              }
        | _ -> (
            match typed_lookup_logic registry scope name with
            | Some logic_symbol ->
                if List.length arguments <> List.length logic_symbol.arguments
                then
                  typed_error ~loc "logical predicate `%s` expects %d arguments"
                    name
                    (List.length logic_symbol.arguments);
                let arguments =
                  List.map2
                    (fun expected expression -> elaborate ~expected expression)
                    logic_symbol.arguments arguments
                in
                finish ?expected ~loc
                  {
                    desc = Application (Logic logic_symbol, arguments);
                    sort = logic_symbol.result;
                  }
            | None -> typed_error ~loc "unknown logical predicate `%s`" name))
    | Pexp_field (record, { txt; _ }) ->
        let name = longident_last txt in
        let record = elaborate record in
        let family, index =
          match Hashtbl.find_opt registry.Typed_core.fields_by_name name with
          | Some entry -> entry
          | None -> typed_error ~loc "unknown logical record field `%s`" name
        in
        let candidates =
          List.concat_map
            (fun (datatype : Typed_core.datatype) -> datatype.constructors)
            registry.datatypes
          |> List.filter (fun constructor ->
              let constructor : Typed_core.constructor = constructor in
              constructor.Typed_core.symbol.key = family.symbol.key
              && constructor.result = record.sort)
        in
        let constructor =
          match candidates with
          | [ constructor ] -> constructor
          | [] ->
              typed_error ~loc
                "record field `%s` does not belong to logic sort %s" name
                (typed_smt_sort record.sort)
          | _ -> typed_error ~loc "record field `%s` remains ambiguous" name
        in
        let sort = List.nth constructor.arguments index in
        finish ?expected ~loc
          {
            desc = Application (Selector (constructor, index), [ record ]);
            sort;
          }
    | _ -> typed_error ~loc "unsupported refinement formula"
  in
  try elaborate ~expected expression
  with Logic_needs_expected (loc, construct) ->
    typed_error ~loc "%s needs an expected logic sort" construct

let rec logic_term_smt (term : Logic_term.t) =
  let open Logic_term in
  match term.desc with
  | Variable variable -> variable
  | Integer value -> string_of_int value
  | Boolean value -> string_of_bool value
  | Application (head, arguments) ->
      let name =
        match head with
        | Builtin name -> name
        | Logic symbol -> typed_logic_name symbol
        | Constructor constructor -> typed_constructor_name constructor
        | Selector (constructor, index) -> typed_selector constructor index
      in
      let arguments = List.map logic_term_smt arguments in
      if arguments = [] then name else app name arguments

let typed_formula ?scope ?expected registry env expression =
  elaborate_formula ?scope ?expected registry env expression |> logic_term_smt

let formula_theory_symbols ?scope ?expected registry env expression =
  elaborate_formula ?scope ?expected registry env expression
  |> Logic_term.theory_symbols

let slice_program_theory (program : Typed_core.program) ~roots =
  let registry = program.registry in
  let artifacts_by_name = Hashtbl.create 16 in
  List.iter
    (fun (artifact : Refined_types.proof_artifact) ->
      Hashtbl.replace artifacts_by_name artifact.lemma_name artifact)
    registry.proof_artifacts;
  let statement kind (axiom : Typed_core.axiom) =
    let formula =
      parse_formula ~filename:axiom.loc.file
        ~loc:(location_of_span axiom.loc)
        axiom.body
    in
    let env =
      List.map
        (fun (name, sort) -> (name, (smt_identifier name, sort)))
        axiom.variables
    in
    let symbols =
      formula_theory_symbols ~scope:axiom.scope registry env formula
      |> List.sort_uniq String.compare
    in
    let requires =
      match kind with
      | `Axiom -> []
      | `Lemma -> (
          match Hashtbl.find_opt artifacts_by_name axiom.axiom_name with
          | Some artifact ->
              artifact.trusted_axioms @ artifact.checked_dependencies
          | None -> [])
    in
    Theory_slice.{ name = axiom.axiom_name; symbols; requires }
  in
  let axioms = List.rev registry.axioms in
  let lemmas = List.rev registry.checked_lemmas in
  let statements =
    List.map (statement `Axiom) axioms @ List.map (statement `Lemma) lemmas
  in
  let slice = Theory_slice.close ~roots statements in
  let selected_name name = List.mem name slice.statement_names in
  let selected_symbol symbol = List.mem symbol slice.symbols in
  let axioms =
    List.filter (fun axiom -> selected_name axiom.Typed_core.axiom_name) axioms
  in
  let checked_lemmas =
    List.filter (fun lemma -> selected_name lemma.Typed_core.axiom_name) lemmas
  in
  let proof_artifacts =
    List.rev registry.proof_artifacts
    |> List.filter (fun artifact -> selected_name artifact.lemma_name)
  in
  let logic_by_name = Hashtbl.create 16 in
  Hashtbl.iter
    (fun name (logic_symbol : Typed_core.logic_symbol) ->
      if selected_symbol logic_symbol.logic_name.key then
        Hashtbl.replace logic_by_name name logic_symbol)
    registry.logic_by_name;
  let datatypes =
    List.filter
      (fun (datatype : Typed_core.datatype) ->
        List.exists
          (fun (constructor : Typed_core.constructor) ->
            selected_symbol constructor.symbol.key)
          datatype.constructors)
      registry.datatypes
  in
  let registry =
    {
      registry with
      logic_by_name;
      axioms = List.rev axioms;
      checked_lemmas = List.rev checked_lemmas;
      proof_artifacts = List.rev proof_artifacts;
      datatypes;
    }
  in
  ({ program with registry }, slice.symbols)
