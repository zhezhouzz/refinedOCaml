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
    | Some { Parsetree.pexp_desc = Pexp_tuple expressions; _ } -> expressions
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

type smt_value = { term : string; refinement : Generic_refinement.type_ option }

let typed_pattern_smt env scrutinee pattern =
  let rec translate env scrutinee = function
    | Typed_core.Pat_any -> ("true", env)
    | Pat_var symbol ->
        ("true", (symbol.key, { term = scrutinee; refinement = None }) :: env)
    | Pat_alias (inner, symbol) ->
        let guard, env = translate env scrutinee inner in
        (guard, (symbol.key, { term = scrutinee; refinement = None }) :: env)
    | Pat_int value -> (app "=" [ scrutinee; string_of_int value ], env)
    | Pat_bool value -> (app "=" [ scrutinee; string_of_bool value ], env)
    | Pat_tuple (sort, patterns) ->
        let guards, env =
          List.fold_left2
            (fun (guards, env) index pattern ->
              let guard, env =
                translate env
                  (app (typed_tuple_selector sort index) [ scrutinee ])
                  pattern
              in
              (guard :: guards, env))
            ([], env)
            (List.init (List.length patterns) Fun.id)
            patterns
        in
        (and_ guards, env)
    | Pat_construct (constructor, patterns) ->
        let guards, env =
          List.fold_left2
            (fun (guards, env) index pattern ->
              let guard, env =
                translate env
                  (app (typed_selector constructor index) [ scrutinee ])
                  pattern
              in
              (guard :: guards, env))
            ([], env)
            (List.init (List.length patterns) Fun.id)
            patterns
        in
        (and_ (app (typed_recognizer constructor) [ scrutinee ] :: guards), env)
  in
  translate env scrutinee pattern

type generic_call_state = {
  runtime_declarations : (string, string list * string) Hashtbl.t;
  mutable side_conditions : string list;
  mutable summary_assumptions : string list;
  mutable ghost_instantiations : string list;
  mutable used_theory_symbols : string list;
  mutable semantic_assumptions : string list;
  mutable local_initial_values : (string * string) list;
}

let new_generic_call_state () =
  {
    runtime_declarations = Hashtbl.create 8;
    side_conditions = [];
    summary_assumptions = [];
    ghost_instantiations = [];
    used_theory_symbols = [];
    semantic_assumptions = [];
    local_initial_values = [];
  }

let use_theory_symbol state symbol =
  if not (List.mem symbol state.used_theory_symbols) then
    state.used_theory_symbols <- symbol :: state.used_theory_symbols

let rec use_pattern_theory state = function
  | Typed_core.Pat_construct (constructor, patterns) ->
      use_theory_symbol state constructor.symbol.key;
      List.iter (use_pattern_theory state) patterns
  | Pat_tuple (_, patterns) -> List.iter (use_pattern_theory state) patterns
  | Pat_alias (pattern, _) -> use_pattern_theory state pattern
  | Pat_any | Pat_var _ | Pat_int _ | Pat_bool _ -> ()

let rec generic_term_smt =
  let open Generic_refinement in
  function
  | Integer integer -> string_of_int integer
  | Boolean boolean -> string_of_bool boolean
  | Variable variable -> smt_identifier variable
  | Not term -> app "not" [ generic_term_smt term ]
  | And terms -> and_ (List.map generic_term_smt terms)
  | Or terms -> or_ (List.map generic_term_smt terms)
  | Equal (left, right) ->
      app "=" [ generic_term_smt left; generic_term_smt right ]
  | Add (left, right) ->
      app "+" [ generic_term_smt left; generic_term_smt right ]
  | Greater (left, right) ->
      app ">" [ generic_term_smt left; generic_term_smt right ]
  | Apply (function_, argument) ->
      app (generic_term_smt function_) [ generic_term_smt argument ]
  | Generic generic -> invalid_arg ("unelaborated generic refinement " ^ generic)
  | Evar evar -> invalid_arg ("unsolved generic refinement " ^ evar)
  | Lambda _ -> invalid_arg "refinement lambda escaped beta-reduction"

let generic_error ~loc =
  let open Generic_refinement in
  function
  | Ill_sorted message | Type_mismatch message ->
      typed_error_at loc "%s" message
  | Ill_formed_hindley generic ->
      typed_error_at loc "Hindley generic `%s` is not value-dependent" generic
  | Ill_formed_horn generic ->
      typed_error_at loc "Horn generic `%s` is not in a positive position"
        generic
  | Arity_mismatch ->
      typed_error_at loc "generic scheme application arity mismatch"
  | Unsolved_hindley generic ->
      typed_error_at loc "Hindley generic `%s` was not solved by its arguments"
        generic
  | Unsolved_horn generic ->
      typed_error_at loc "Horn generic `%s` has no solvable lower bound" generic
  | Unsupported_horn_constraint generic ->
      typed_error_at loc "Horn constraints for `%s` left the positive fragment"
        generic
  | Horn_fixpoint_did_not_converge iterations ->
      typed_error_at loc "Horn fixpoint did not converge in %d iterations"
        iterations
  | Cyclic_instantiation evar ->
      typed_error_at loc "cyclic Hindley instantiation `%s`" evar

let generic_constraint_smt ~loc (constraint_ : Generic_refinement.constraint_) =
  try
    app "=>"
      [
        generic_term_smt constraint_.assumption;
        generic_term_smt constraint_.requirement;
      ]
  with Invalid_argument message ->
    typed_error_at loc "generic call constraint is not first-order: %s" message

let under_path path condition =
  match path with [] -> condition | _ -> app "=>" [ and_ path; condition ]

let instantiate_function_at_call ~loc (function_def : Typed_core.function_def)
    arguments result_sort =
  let open Typed_core in
  let substitutions = Sort_evars.create () in
  let unify formal actual =
    match Sort_evars.unify substitutions ~formal ~actual with
    | Ok () -> ()
    | Error (Occurs (variable, actual)) ->
        typed_error_at loc "cyclic call-site type instance `%s` in %s" variable
          (typed_smt_sort actual)
    | Error (Shape_mismatch (formal, actual)) ->
        typed_error_at loc "call-site type mismatch: expected %s but got %s"
          (typed_smt_sort formal) (typed_smt_sort actual)
  in
  List.iter2
    (fun (_, formal) (actual : Typed_core.expr) -> unify formal actual.sort)
    function_def.arguments arguments;
  unify function_def.result result_sort;
  let substitute = Sort_evars.substitute substitutions in
  let constructor (constructor : Typed_core.constructor) =
    {
      constructor with
      arguments = List.map substitute constructor.arguments;
      result = substitute constructor.result;
    }
  in
  let constructor_for_result constructor_ result =
    let constructor_ = constructor constructor_ in
    let local = Sort_evars.create () in
    match Sort_evars.unify local ~formal:constructor_.result ~actual:result with
    | Ok () ->
        let substitute = Sort_evars.substitute local in
        {
          constructor_ with
          arguments = List.map substitute constructor_.arguments;
          result;
        }
    | Error _ -> { constructor_ with result }
  in
  let rec pattern expected = function
    | Typed_core.Pat_tuple (_, patterns) ->
        let elements =
          match expected with
          | S_tuple elements when List.length elements = List.length patterns ->
              elements
          | _ -> List.map (fun _ -> S_unit) patterns
        in
        Pat_tuple (expected, List.map2 pattern elements patterns)
    | Pat_construct (constructor_, patterns) ->
        let constructor_ = constructor_for_result constructor_ expected in
        Pat_construct
          (constructor_, List.map2 pattern constructor_.arguments patterns)
    | Pat_alias (inner, symbol) -> Pat_alias (pattern expected inner, symbol)
    | (Pat_any | Pat_var _ | Pat_int _ | Pat_bool _) as pattern -> pattern
  in
  let rec map_expression (current : Typed_core.expr) =
    let sort = substitute current.sort in
    let desc =
      match current.desc with
      | (Var _ | Int _ | Bool _ | Deref _) as desc -> desc
      | Raise (exception_, payload) ->
          Raise (exception_, Option.map map_expression payload)
      | Perform (operation, payload) ->
          Perform (operation, Option.map map_expression payload)
      | Tuple expressions -> Tuple (List.map map_expression expressions)
      | Construct (constructor_, expressions) ->
          Construct
            ( constructor_for_result constructor_ sort,
              List.map map_expression expressions )
      | Choose expressions -> Choose (List.map map_expression expressions)
      | Apply (symbol, expressions) ->
          Apply (symbol, List.map map_expression expressions)
      | If (condition, if_true, if_false) ->
          If
            ( map_expression condition,
              map_expression if_true,
              map_expression if_false )
      | Let (symbol, value, body) ->
          Let (symbol, map_expression value, map_expression body)
      | Match (scrutinee, cases) ->
          let scrutinee = map_expression scrutinee in
          Match
            ( scrutinee,
              List.map
                (fun (pattern_, body) ->
                  (pattern scrutinee.sort pattern_, map_expression body))
                cases )
      | Record (constructor_, expressions) ->
          Record
            ( constructor_for_result constructor_ sort,
              List.map map_expression expressions )
      | Field (constructor_, index, record) ->
          let record = map_expression record in
          Field (constructor_for_result constructor_ record.sort, index, record)
      | Try (body, cases) ->
          Try
            ( map_expression body,
              List.map
                (fun (pattern, handler) -> (pattern, map_expression handler))
                cases )
      | Let_ref (symbol, sort, initial, body) ->
          Let_ref
            ( symbol,
              substitute sort,
              map_expression initial,
              map_expression body )
      | Ref (sort, initial) -> Ref (substitute sort, map_expression initial)
      | Assign (symbol, value) -> Assign (symbol, map_expression value)
      | Sequence (first, second) ->
          Sequence (map_expression first, map_expression second)
      | Handle (body, handlers) ->
          let rec map_action = function
            | Typed_core.Abort handler ->
                Typed_core.Abort (map_expression handler)
            | Typed_core.Resume value ->
                Typed_core.Resume (map_expression value)
            | Typed_core.Conditional (condition, if_true, if_false) ->
                Typed_core.Conditional
                  ( map_expression condition,
                    map_action if_true,
                    map_action if_false )
          in
          Handle
            ( map_expression body,
              List.map
                (fun (operation, payload, action) ->
                  (operation, payload, map_action action))
                handlers )
    in
    { current with desc; sort }
  in
  {
    function_def with
    arguments =
      List.map
        (fun (symbol, sort) -> (symbol, substitute sort))
        function_def.arguments;
    result = substitute function_def.result;
    body = map_expression function_def.body;
    contracts =
      List.map
        (fun (contract : Typed_core.contract) ->
          {
            contract with
            ghosts =
              List.map
                (fun (name, sort) -> (name, substitute sort))
                contract.ghosts;
          })
        function_def.contracts;
  }

let rec typed_expr_smt_with_choices (program : Typed_core.program) analysis mode
    current_function path call_stack choices generic_calls env expression =
  let registry = program.registry in
  let _sort = expression.Typed_core.sort in
  let recurse =
    typed_expr_smt_with_choices program analysis mode current_function path
      call_stack choices generic_calls env
  in
  let make ?(refinement = expression.Typed_core.refinement) term =
    { term; refinement }
  in
  let recurse_term expression = (recurse expression).term in
  match expression.Typed_core.desc with
  | Var symbol -> (
      match List.assoc_opt symbol.key env with
      | Some value -> (
          match expression.refinement with
          | Some refinement -> { value with refinement = Some refinement }
          | None -> value)
      | None ->
          typed_error_at expression.loc "unsupported global value `%s`"
            symbol.display)
  | Int value -> make (string_of_int value)
  | Bool value -> make (string_of_bool value)
  | Construct (constructor, arguments) | Record (constructor, arguments) ->
      use_theory_symbol generic_calls constructor.symbol.key;
      let arguments = List.map recurse_term arguments in
      make
        (if arguments = [] then typed_constructor_name constructor
         else app (typed_constructor_name constructor) arguments)
  | Choose [ left; right ] ->
      let name = "choice_" ^ string_of_int (List.length !choices) in
      choices := (name, Typed_core.S_bool) :: !choices;
      make (app "ite" [ name; recurse_term left; recurse_term right ])
  | Choose _ ->
      typed_error_at expression.loc
        "the MVP choose primitive currently requires exactly two alternatives"
  | Apply (symbol, arguments)
    when Hashtbl.mem program.registry.generic_schemes_by_name symbol.key ->
      let scheme =
        Hashtbl.find program.registry.generic_schemes_by_name symbol.key
      in
      let argument_values = List.map recurse arguments in
      let actual_types =
        List.map
          (fun ((argument : Typed_core.expr), value) ->
            match value.refinement with
            | Some refinement -> refinement
            | None ->
                typed_error_at argument.loc
                  "argument to generic `%s` needs [@refined.type]"
                  symbol.display)
          (List.combine arguments argument_values)
      in
      let elaboration =
        match Generic_refinement.elaborate_application scheme actual_types with
        | Ok elaboration -> elaboration
        | Error error -> generic_error ~loc:expression.loc error
      in
      let runtime_name = "F_" ^ smt_identifier symbol.key in
      Hashtbl.replace generic_calls.runtime_declarations runtime_name
        ( List.map
            (fun (argument : Typed_core.expr) -> typed_smt_sort argument.sort)
            arguments,
          typed_smt_sort expression.sort );
      generic_calls.side_conditions <-
        List.rev_append
          (List.map
             (fun constraint_ ->
               generic_constraint_smt ~loc:expression.loc constraint_
               |> under_path path)
             elaboration.constraints)
          generic_calls.side_conditions;
      generic_calls.ghost_instantiations <-
        List.rev_append
          (List.map
             (fun (instantiation : Generic_refinement.instantiation) ->
               Printf.sprintf "%s.%s=%s" symbol.display instantiation.generic
                 (Generic_refinement.string_of_term instantiation.refinement))
             elaboration.instantiations)
          generic_calls.ghost_instantiations;
      make ~refinement:(Some elaboration.result)
        (app runtime_name (List.map (fun value -> value.term) argument_values))
  | Apply (symbol, [ left; right ]) -> (
      if symbol.display = "==" || symbol.display = "!=" then
        match
          ( reference_content_sort left.Typed_core.sort,
            reference_content_sort right.Typed_core.sort )
        with
        | Some left_sort, Some right_sort
          when typed_smt_sort left_sort = typed_smt_sort right_sort ->
            make
              (app
                 (if symbol.display = "==" then "=" else "distinct")
                 [ recurse_term left; recurse_term right ])
        | _ ->
            typed_error_at expression.loc
              "physical equality is supported only between references of the \
               same content sort"
      else
        match binary_operator symbol.display with
        | Some operator ->
            make (app operator [ recurse_term left; recurse_term right ])
        | None -> (
            match typed_lookup_logic registry [] symbol.key with
            | Some logic_symbol ->
                use_theory_symbol generic_calls logic_symbol.logic_name.key;
                if List.length logic_symbol.arguments <> 2 then
                  typed_error_at expression.loc
                    "logical predicate `%s` has an unsupported application \
                     arity"
                    symbol.display;
                make
                  (app
                     (typed_logic_name logic_symbol)
                     [ recurse_term left; recurse_term right ])
            | None ->
                typed_inline_call program analysis mode current_function path
                  call_stack choices generic_calls env expression symbol
                  [ left; right ]))
  | Apply (symbol, [ argument ]) when symbol.display = "not" ->
      make (app "not" [ recurse_term argument ])
  | Apply (symbol, _) -> (
      let arguments =
        match expression.desc with
        | Apply (_, arguments) -> arguments
        | _ -> assert false
      in
      match typed_lookup_logic registry [] symbol.key with
      | Some logic_symbol ->
          use_theory_symbol generic_calls logic_symbol.logic_name.key;
          if List.length arguments <> List.length logic_symbol.arguments then
            typed_error_at expression.loc
              "logical predicate `%s` has an unsupported application arity"
              symbol.display;
          make
            (app
               (typed_logic_name logic_symbol)
               (List.map recurse_term arguments))
      | None ->
          typed_inline_call program analysis mode current_function path
            call_stack choices generic_calls env expression symbol arguments)
  | If (condition, if_true, if_false) ->
      let condition = recurse condition in
      let branch branch_path branch =
        typed_expr_smt_with_choices program analysis mode current_function
          (branch_path :: path) call_stack choices generic_calls env branch
      in
      let if_true = branch condition.term if_true in
      let if_false = branch (app "not" [ condition.term ]) if_false in
      let refinement =
        if if_true.refinement = if_false.refinement then if_true.refinement
        else expression.refinement
      in
      make ~refinement
        (app "ite" [ condition.term; if_true.term; if_false.term ])
  | Let (symbol, value, body) ->
      let value = recurse value in
      typed_expr_smt_with_choices program analysis mode current_function path
        call_stack choices generic_calls
        ((symbol.key, value) :: env)
        body
  | Match (scrutinee, cases) ->
      let scrutinee = recurse_term scrutinee in
      List.iter
        (fun (pattern, _) -> use_pattern_theory generic_calls pattern)
        cases;
      let translated =
        let rec translate previous = function
          | [] -> []
          | (pattern, body) :: rest ->
              let guard, case_env = typed_pattern_smt env scrutinee pattern in
              let effective_guard =
                match previous with
                | [] -> guard
                | _ -> and_ [ guard; app "not" [ or_ previous ] ]
              in
              let body =
                typed_expr_smt_with_choices program analysis mode
                  current_function (effective_guard :: path) call_stack choices
                  generic_calls case_env body
              in
              (guard, body) :: translate (guard :: previous) rest
        in
        translate [] cases
      in
      let refinement =
        match translated with
        | [] -> expression.refinement
        | (_, first) :: rest ->
            if
              List.for_all
                (fun (_, value) -> value.refinement = first.refinement)
                rest
            then first.refinement
            else expression.refinement
      in
      let rec tree = function
        | [] -> typed_error_at expression.loc "empty match"
        | [ (_, body) ] -> body.term
        | (guard, body) :: rest -> app "ite" [ guard; body.term; tree rest ]
      in
      make ~refinement (tree translated)
  | Field (constructor, index, record) ->
      use_theory_symbol generic_calls constructor.symbol.key;
      make (app (typed_selector constructor index) [ recurse_term record ])
  | Tuple elements ->
      make
        (app
           (typed_tuple_constructor expression.sort)
           (List.map recurse_term elements))
  | Raise _ | Try _ | Ref _ | Let_ref _ | Deref _ | Assign _ | Sequence _
  | Perform _ | Handle _ ->
      typed_error_at expression.loc
        "exception outcome escaped the relational translator"

and typed_inline_call program analysis mode current_function path call_stack
    choices generic_calls env expression symbol arguments =
  let function_def =
    List.find_opt
      (fun (function_def : Typed_core.function_def) ->
        function_def.symbol.key = symbol.Typed_core.key)
      program.Typed_core.functions
  in
  match function_def with
  | None ->
      typed_error_at expression.Typed_core.loc
        "call to `%s` needs a refinement summary" symbol.display
  | Some function_def ->
      if List.length arguments <> List.length function_def.arguments then
        typed_error_at expression.loc
          "call to `%s` has unsupported partial arity" symbol.display;
      let function_def =
        instantiate_function_at_call ~loc:expression.loc function_def arguments
          expression.sort
      in
      let call_program = typed_monomorphize_datatypes program function_def in
      List.iter
        (fun (datatype : Typed_core.datatype) ->
          if
            not
              (List.exists
                 (fun (existing : Typed_core.datatype) ->
                   existing.owner = datatype.owner)
                 program.registry.datatypes)
          then
            program.registry.datatypes <- datatype :: program.registry.datatypes)
        call_program.registry.datatypes;
      let values =
        List.map
          (typed_expr_smt_with_choices program analysis mode current_function
             path call_stack choices generic_calls env)
          arguments
      in
      let terms = List.map (fun value -> value.term) values in
      let recursive =
        Function_analysis.is_recursive_edge analysis
          ~caller:current_function.Typed_core.symbol.key ~callee:symbol.key
      in
      let over_contracts =
        List.filter
          (fun (contract : Typed_core.contract) -> contract.mode = Over)
          function_def.contracts
      in
      let constructive_under_contracts =
        List.filter
          (fun (contract : Typed_core.contract) ->
            contract.mode = Under
            && (contract.witnesses <> [] || contract.witness_relation <> None))
          function_def.contracts
      in
      if mode = Over && over_contracts <> [] then (
        let summary =
          match over_contracts with
          | [ summary ] -> summary
          | _ ->
              typed_error_at expression.loc
                "call to `%s` has ambiguous safety summaries" symbol.display
        in
        let result = "call_result_" ^ string_of_int (List.length !choices) in
        choices := (result, function_def.result) :: !choices;
        let formula_env =
          List.map2
            (fun ((argument : Typed_core.symbol), sort) term ->
              (argument.display, (term, sort)))
            function_def.arguments terms
        in
        let translate formula =
          let formula =
            parse_formula ~filename:summary.loc.file
              ~loc:(location_of_span summary.loc)
              formula
          in
          formula_theory_symbols program.registry formula_env formula
          |> List.iter (use_theory_symbol generic_calls);
          typed_formula program.registry formula_env formula
        in
        let pre = translate summary.pre in
        let post =
          let formula =
            parse_formula ~filename:summary.loc.file
              ~loc:(location_of_span summary.loc)
              summary.post
          in
          formula_theory_symbols program.registry
            (("result", (result, function_def.result)) :: formula_env)
            formula
          |> List.iter (use_theory_symbol generic_calls);
          typed_formula program.registry
            (("result", (result, function_def.result)) :: formula_env)
            formula
        in
        generic_calls.side_conditions <-
          under_path path pre :: generic_calls.side_conditions;
        generic_calls.summary_assumptions <-
          under_path path post :: generic_calls.summary_assumptions;
        (if recursive then
           let callee_measure =
             match function_def.measure with
             | Some measure -> measure
             | None ->
                 typed_error_at expression.loc
                   "recursive callee `%s` needs [@refined.measure]"
                   symbol.display
           in
           let caller_measure =
             match current_function.Typed_core.measure with
             | Some measure -> measure
             | None ->
                 typed_error_at expression.loc
                   "recursive caller `%s` needs [@refined.measure]"
                   current_function.symbol.display
           in
           let callee_measure_term =
             List.find_map
               (fun (((argument : Typed_core.symbol), _), term) ->
                 if argument.key = callee_measure.key then Some term else None)
               (List.combine function_def.arguments terms)
             |> Option.get
           in
           let caller_measure_term =
             match List.assoc_opt caller_measure.key env with
             | Some value -> value.term
             | None -> assert false
           in
           generic_calls.side_conditions <-
             under_path path
               (and_
                  [
                    app ">=" [ caller_measure_term; "0" ];
                    app "<" [ callee_measure_term; caller_measure_term ];
                  ])
             :: generic_calls.side_conditions);
        { term = result; refinement = expression.refinement })
      else if mode = Under && constructive_under_contracts <> [] then (
        let summary =
          match constructive_under_contracts with
          | [ summary ] -> summary
          | _ ->
              typed_error_at expression.loc
                "call to `%s` has ambiguous constructive coverage summaries"
                symbol.display
        in
        let formal_names =
          List.map
            (fun ((argument : Typed_core.symbol), _) -> argument.display)
            function_def.arguments
        in
        if
          summary.witnesses <> []
          && List.sort String.compare (List.map fst summary.witnesses)
             <> List.sort String.compare formal_names
        then
          typed_error_at expression.loc
            "coverage summary for `%s` has incomplete witnesses" symbol.display;
        let result = "call_result_" ^ string_of_int (List.length !choices) in
        choices := (result, function_def.result) :: !choices;
        let result_env = [ ("result", (result, function_def.result)) ] in
        let ghost_env =
          List.map
            (fun (name, sort) ->
              let term =
                "call_ghost_" ^ smt_identifier name ^ "_"
                ^ string_of_int (List.length !choices)
              in
              choices := (term, sort) :: !choices;
              (name, (term, sort)))
            summary.ghosts
        in
        let witness_env = ghost_env @ result_env in
        let formula_env =
          List.map2
            (fun ((formal : Typed_core.symbol), sort) term ->
              (formal.display, (term, sort)))
            function_def.arguments terms
        in
        let parse text =
          parse_formula ~filename:summary.loc.file
            ~loc:(location_of_span summary.loc)
            text
        in
        let post_formula = parse summary.post in
        formula_theory_symbols program.registry result_env post_formula
        |> List.iter (use_theory_symbol generic_calls);
        let constraints =
          typed_formula program.registry result_env post_formula
          ::
          (if summary.witnesses = [] then []
           else
             List.map2
               (fun ((formal : Typed_core.symbol), sort) actual ->
                 let witness =
                   parse (List.assoc formal.display summary.witnesses)
                 in
                 formula_theory_symbols ~expected:sort program.registry
                   witness_env witness
                 |> List.iter (use_theory_symbol generic_calls);
                 app "="
                   [
                     actual;
                     typed_formula ~expected:sort program.registry witness_env
                       witness;
                   ])
               function_def.arguments terms)
        in
        let constraints =
          match summary.witness_relation with
          | None -> constraints
          | Some relation ->
              let relation = parse relation in
              let relation_env = witness_env @ formula_env in
              formula_theory_symbols program.registry relation_env relation
              |> List.iter (use_theory_symbol generic_calls);
              typed_formula program.registry relation_env relation
              :: constraints
        in
        generic_calls.summary_assumptions <-
          List.rev_append
            (List.map (under_path path) constraints)
            generic_calls.summary_assumptions;
        (if recursive then
           let callee_measure =
             match function_def.measure with
             | Some measure -> measure
             | None ->
                 typed_error_at expression.loc
                   "recursive coverage callee `%s` needs [@refined.measure]"
                   symbol.display
           in
           let caller_measure =
             match current_function.Typed_core.measure with
             | Some measure -> measure
             | None ->
                 typed_error_at expression.loc
                   "recursive coverage caller `%s` needs [@refined.measure]"
                   current_function.symbol.display
           in
           let callee =
             List.find_map
               (fun (((argument : Typed_core.symbol), _), term) ->
                 if argument.key = callee_measure.key then Some term else None)
               (List.combine function_def.arguments terms)
             |> Option.get
           in
           let caller = (List.assoc caller_measure.key env).term in
           generic_calls.summary_assumptions <-
             under_path path
               (and_ [ app ">=" [ caller; "0" ]; app "<" [ callee; caller ] ])
             :: generic_calls.summary_assumptions);
        { term = result; refinement = expression.refinement })
      else if recursive then
        typed_error_at expression.loc
          (if mode = Under then
             "recursive coverage call to `%s` needs a compositional \
              under-summary"
           else "recursive call to `%s` needs one safety summary")
          symbol.display
      else
        let call_env =
          List.map2
            (fun (argument, _) term -> (argument.Typed_core.key, term))
            function_def.arguments values
        in
        typed_expr_smt_with_choices program analysis mode function_def path
          (symbol.key :: call_stack) choices generic_calls call_env
          function_def.body

let typed_expr_smt program analysis mode function_def env expression =
  let choices = ref [] in
  let generic_calls = new_generic_call_state () in
  let term =
    typed_expr_smt_with_choices program analysis mode function_def [] [] choices
      generic_calls env expression
  in
  (term, List.rev !choices, generic_calls)

let rec typed_has_exception (expression : Typed_core.expr) =
  match expression.desc with
  | Raise _ | Try _ | Ref _ | Let_ref _ | Deref _ | Assign _ | Sequence _
  | Perform _ | Handle _ ->
      true
  | Var _ | Int _ | Bool _ -> false
  | Tuple expressions
  | Construct (_, expressions)
  | Choose expressions
  | Apply (_, expressions)
  | Record (_, expressions) ->
      List.exists typed_has_exception expressions
  | If (condition, if_true, if_false) ->
      List.exists typed_has_exception [ condition; if_true; if_false ]
  | Let (_, value, body) ->
      typed_has_exception value || typed_has_exception body
  | Match (scrutinee, cases) ->
      typed_has_exception scrutinee
      || List.exists (fun (_, body) -> typed_has_exception body) cases
  | Field (_, _, record) -> typed_has_exception record

let typed_requires_relational (program : Typed_core.program) expression =
  let rec check visited (expression : Typed_core.expr) =
    typed_has_exception expression
    ||
    match expression.desc with
    | Apply (symbol, arguments) ->
        List.exists (check visited) arguments
        ||
        if List.mem symbol.key visited then false
        else
          Option.fold ~none:false
            ~some:(fun (callee : Typed_core.function_def) ->
              check (symbol.key :: visited) callee.body)
            (List.find_opt
               (fun (callee : Typed_core.function_def) ->
                 callee.symbol.key = symbol.key)
               program.functions)
    | Tuple expressions
    | Construct (_, expressions)
    | Choose expressions
    | Record (_, expressions) ->
        List.exists (check visited) expressions
    | If (condition, if_true, if_false) ->
        List.exists (check visited) [ condition; if_true; if_false ]
    | Let (_, value, body) | Sequence (value, body) ->
        check visited value || check visited body
    | Match (scrutinee, cases) ->
        check visited scrutinee
        || List.exists (fun (_, body) -> check visited body) cases
    | Field (_, _, record) | Assign (_, record) -> check visited record
    | Ref _ -> true
    | Let_ref (_, _, initial, body) ->
        check visited initial || check visited body
    | Try _ | Raise _ | Perform _ | Handle _ | Deref _ -> true
    | Var _ | Int _ | Bool _ -> false
  in
  check [] expression

let typed_local_cells expression =
  let rec collect cells (expression : Typed_core.expr) =
    match expression.desc with
    | Let_ref (symbol, sort, initial, body) ->
        collect
          ((symbol.display, "ref_" ^ smt_identifier symbol.key, sort)
          :: collect cells initial)
          body
    | Ref (_, initial) -> collect cells initial
    | Let (_, value, body) | Sequence (value, body) ->
        collect (collect cells value) body
    | If (condition, if_true, if_false) ->
        collect (collect (collect cells condition) if_true) if_false
    | Try (body, cases) ->
        List.fold_left
          (fun cells (_, handler) -> collect cells handler)
          (collect cells body) cases
    | Match (body, cases) ->
        List.fold_left
          (fun cells (_, handler) -> collect cells handler)
          (collect cells body) cases
    | Tuple expressions
    | Construct (_, expressions)
    | Choose expressions
    | Apply (_, expressions)
    | Record (_, expressions) ->
        List.fold_left collect cells expressions
    | Assign (_, value) | Field (_, _, value) -> collect cells value
    | Var _ | Int _ | Bool _ | Raise (_, None) | Perform (_, None) | Deref _ ->
        cells
    | Raise (_, Some payload) | Perform (_, Some payload) ->
        collect cells payload
    | Handle (body, handlers) ->
        let rec collect_action cells = function
          | Typed_core.Abort handler | Typed_core.Resume handler ->
              collect cells handler
          | Typed_core.Conditional (condition, if_true, if_false) ->
              collect_action
                (collect_action (collect cells condition) if_true)
                if_false
        in
        List.fold_left
          (fun cells (_, _, action) -> collect_action cells action)
          (collect cells body) handlers
  in
  collect [] expression |> List.sort_uniq compare

let typed_reference_arguments (function_def : Typed_core.function_def) =
  List.filter_map
    (fun ((symbol : Typed_core.symbol), sort) ->
      Option.map
        (fun content -> (symbol.display, symbol.key, content))
        (reference_content_sort sort))
    function_def.arguments

let typed_expression_reference_sorts ?registry expression =
  let rec reachable_content_sorts registry visited sort =
    match reference_content_sort sort with
    | Some content -> [ content ]
    | None -> (
        match sort with
        | Typed_core.S_tuple sorts ->
            List.concat_map (reachable_content_sorts registry visited) sorts
        | S_app _ ->
            let sort_name = typed_smt_sort sort in
            if List.mem sort_name visited then []
            else
              registry.Typed_core.datatypes
              |> List.find_opt (fun (datatype : Typed_core.datatype) ->
                  typed_smt_sort datatype.owner = sort_name)
              |> Option.fold ~none:[]
                   ~some:(fun (datatype : Typed_core.datatype) ->
                     datatype.constructors
                     |> List.concat_map
                          (fun (constructor : Typed_core.constructor) ->
                            List.concat_map
                              (reachable_content_sorts registry
                                 (sort_name :: visited))
                              constructor.arguments))
        | S_int | S_bool | S_unit | S_var _ -> [])
  in
  let rec collect sorts (expression : Typed_core.expr) =
    let sorts =
      match reference_content_sort expression.sort with
      | Some sort -> sort :: sorts
      | None -> (
          match registry with
          | None -> sorts
          | Some registry ->
              List.rev_append
                (reachable_content_sorts registry [] expression.sort)
                sorts)
    in
    match expression.desc with
    | Let_ref (_, sort, initial, body) ->
        collect (collect (sort :: sorts) initial) body
    | Ref (sort, initial) -> collect (sort :: sorts) initial
    | Let (_, value, body) | Sequence (value, body) ->
        collect (collect sorts value) body
    | If (condition, if_true, if_false) ->
        collect (collect (collect sorts condition) if_true) if_false
    | Try (body, cases) ->
        List.fold_left
          (fun sorts (_, branch) -> collect sorts branch)
          (collect sorts body) cases
    | Match (body, cases) ->
        List.fold_left
          (fun sorts (_, branch) -> collect sorts branch)
          (collect sorts body) cases
    | Tuple expressions
    | Construct (_, expressions)
    | Choose expressions
    | Apply (_, expressions)
    | Record (_, expressions) ->
        List.fold_left collect sorts expressions
    | Assign (_, value) | Field (_, _, value) -> collect sorts value
    | Raise (_, Some payload) | Perform (_, Some payload) ->
        collect sorts payload
    | Handle (body, handlers) ->
        let rec action sorts = function
          | Typed_core.Abort expression | Resume expression ->
              collect sorts expression
          | Conditional (condition, if_true, if_false) ->
              action (action (collect sorts condition) if_true) if_false
        in
        List.fold_left
          (fun sorts (_, _, handler) -> action sorts handler)
          (collect sorts body) handlers
    | Var _ | Int _ | Bool _ | Deref _ | Raise (_, None) | Perform (_, None) ->
        sorts
  in
  collect [] expression
  |> List.sort_uniq (fun left right ->
      String.compare (typed_smt_sort left) (typed_smt_sort right))

let typed_function_reference_sorts ?registry function_def =
  List.map (fun (_, _, sort) -> sort) (typed_reference_arguments function_def)
  @ typed_expression_reference_sorts ?registry function_def.Typed_core.body
  |> List.sort_uniq (fun left right ->
      String.compare (typed_smt_sort left) (typed_smt_sort right))

let typed_expression_sorts expression =
  let rec collect sorts (expression : Typed_core.expr) =
    let sorts = expression.sort :: sorts in
    match expression.desc with
    | Ref (sort, initial) -> collect (sort :: sorts) initial
    | Let_ref (_, sort, initial, body) ->
        collect (collect (sort :: sorts) initial) body
    | Let (_, value, body) | Sequence (value, body) ->
        collect (collect sorts value) body
    | If (condition, if_true, if_false) ->
        collect (collect (collect sorts condition) if_true) if_false
    | Try (body, cases) ->
        List.fold_left
          (fun sorts (_, branch) -> collect sorts branch)
          (collect sorts body) cases
    | Match (body, cases) ->
        List.fold_left
          (fun sorts (_, branch) -> collect sorts branch)
          (collect sorts body) cases
    | Tuple expressions | Choose expressions | Apply (_, expressions) ->
        List.fold_left collect sorts expressions
    | Construct (constructor, expressions) | Record (constructor, expressions)
      ->
        List.fold_left collect
          ((constructor.result :: constructor.arguments) @ sorts)
          expressions
    | Assign (_, value) -> collect sorts value
    | Field (constructor, _, value) ->
        collect ((constructor.result :: constructor.arguments) @ sorts) value
    | Raise (_, Some payload) | Perform (_, Some payload) ->
        collect sorts payload
    | Handle (body, handlers) ->
        let rec action sorts = function
          | Typed_core.Abort expression | Resume expression ->
              collect sorts expression
          | Conditional (condition, if_true, if_false) ->
              action (action (collect sorts condition) if_true) if_false
        in
        List.fold_left
          (fun sorts (_, _, handler) -> action sorts handler)
          (collect sorts body) handlers
    | Var _ | Int _ | Bool _ | Deref _ | Raise (_, None) | Perform (_, None) ->
        sorts
  in
  collect [] expression
  |> List.sort_uniq (fun left right ->
      String.compare (typed_smt_sort left) (typed_smt_sort right))

let heap_key sort = "heap_" ^ smt_identifier (typed_smt_sort sort)
let initial_heap_name sort = "initial_" ^ heap_key sort

let reference_sort sort =
  Typed_core.S_app ({ key = "Stdlib.ref"; display = "ref" }, [ sort ])

let heap_select state identity sort =
  match List.assoc_opt (heap_key sort) state with
  | Some heap -> app "select" [ heap; identity ]
  | None -> invalid_arg ("missing relational heap " ^ heap_key sort)

let heap_store state identity sort value =
  let key = heap_key sort in
  match List.assoc_opt key state with
  | Some heap ->
      (key, app "store" [ heap; identity; value ])
      :: List.remove_assoc key state
  | None -> invalid_arg ("missing relational heap " ^ key)

let heap_store_guarded state guard identity sort value =
  let key = heap_key sort in
  match List.assoc_opt key state with
  | Some heap ->
      let stored = app "store" [ heap; identity; value ] in
      let heap =
        if guard = "true" then stored else app "ite" [ guard; stored; heap ]
      in
      (key, heap) :: List.remove_assoc key state
  | None -> invalid_arg ("missing relational heap " ^ key)

let alias_consistency updates =
  let rec pairs = function
    | [] -> []
    | (identity, sort, value) :: rest ->
        List.filter_map
          (fun (other_identity, other_sort, other_value) ->
            if typed_smt_sort sort <> typed_smt_sort other_sort then None
            else
              Some
                (app "=>"
                   [
                     app "=" [ identity; other_identity ];
                     app "=" [ value; other_value ];
                   ]))
          rest
        @ pairs rest
  in
  pairs updates

let guarded_alias_consistency updates =
  let rec pairs = function
    | [] -> []
    | (identity, sort, value, guard) :: rest ->
        List.filter_map
          (fun (other_identity, other_sort, other_value, other_guard) ->
            if typed_smt_sort sort <> typed_smt_sort other_sort then None
            else
              Some
                (app "=>"
                   [
                     and_
                       [
                         guard;
                         other_guard;
                         app "=" [ identity; other_identity ];
                       ];
                     app "=" [ value; other_value ];
                   ]))
          rest
        @ pairs rest
  in
  pairs updates

let guarded_identity_distinctness identities =
  let rec pairs = function
    | [] -> []
    | (identity, sort, guard) :: rest ->
        List.filter_map
          (fun (other_identity, other_sort, other_guard) ->
            if typed_smt_sort sort <> typed_smt_sort other_sort then None
            else
              Some
                (app "=>"
                   [
                     and_ [ guard; other_guard ];
                     app "distinct" [ identity; other_identity ];
                   ]))
          rest
        @ pairs rest
  in
  pairs identities

let frame_obligations ~initial ~final ~references ~modified =
  references
  |> List.filter_map (fun (_name, identity, sort) ->
      if List.mem identity modified then None
      else
        let possible_aliases =
          references
          |> List.filter_map (fun (_name, candidate, candidate_sort) ->
              if
                List.mem candidate modified
                && typed_smt_sort candidate_sort = typed_smt_sort sort
              then Some candidate
              else None)
        in
        let unchanged =
          app "="
            [
              heap_select final identity sort; heap_select initial identity sort;
            ]
        in
        match possible_aliases with
        | [] -> Some unchanged
        | aliases ->
            Some
              (app "=>"
                 [
                   and_
                     (List.map
                        (fun modified_identity ->
                          app "distinct" [ identity; modified_identity ])
                        aliases);
                   unchanged;
                 ]))

let reference_modified_identities references names =
  references
  |> List.filter_map (fun (name, identity, _sort) ->
      if List.mem name names then Some identity else None)

type returned_reference_path = {
  path : string;
  identity : string;
  content_sort : Typed_core.sort;
  guard : string;
}

let returned_reference_value_name path = "result_value_" ^ smt_identifier path

let sort_reaches_reference registry sort =
  let rec visit visited sort =
    match reference_content_sort sort with
    | Some _ -> true
    | None -> (
        match sort with
        | Typed_core.S_tuple sorts -> List.exists (visit visited) sorts
        | S_app _ ->
            let name = typed_smt_sort sort in
            if List.mem name visited then false
            else
              registry.Typed_core.datatypes @ registry.datatype_templates
              |> List.find_opt (fun (datatype : Typed_core.datatype) ->
                  typed_smt_sort datatype.owner = name
                  ||
                  match (datatype.owner, sort) with
                  | S_app (owner, _), S_app (candidate, _) ->
                      owner.key = candidate.key
                  | _ -> false)
              |> Option.fold ~none:false
                   ~some:(fun (datatype : Typed_core.datatype) ->
                     List.exists
                       (fun (constructor : Typed_core.constructor) ->
                         List.exists
                           (visit (name :: visited))
                           constructor.arguments)
                       datatype.constructors)
        | S_int | S_bool | S_unit | S_var _ -> false)
  in
  visit [] sort

let returned_reference_paths registry ~result_sort ~result =
  let datatype_for sort =
    registry.Typed_core.datatypes
    |> List.find_opt (fun (datatype : Typed_core.datatype) ->
        typed_smt_sort datatype.owner = typed_smt_sort sort)
  in
  let path_name segments = String.concat "." (List.rev segments) in
  let rec collect visited segments guards term sort =
    match reference_content_sort sort with
    | Some content_sort ->
        Ok
          [
            {
              path = path_name segments;
              identity = term;
              content_sort;
              guard = and_ guards;
            };
          ]
    | None -> (
        match sort with
        | Typed_core.S_tuple elements ->
            elements
            |> List.mapi (fun index element ->
                collect visited
                  (string_of_int index :: segments)
                  guards
                  (app (typed_tuple_selector sort index) [ term ])
                  element)
            |> List.fold_left
                 (fun result paths ->
                   match (result, paths) with
                   | Ok result, Ok paths -> Ok (result @ paths)
                   | Error error, _ | _, Error error -> Error error)
                 (Ok [])
        | S_app _ -> (
            match datatype_for sort with
            | None -> Ok []
            | Some datatype ->
                let sort_name = typed_smt_sort sort in
                if List.mem sort_name visited then
                  if sort_reaches_reference registry sort then
                    Error (path_name segments)
                  else Ok []
                else
                  datatype.constructors
                  |> List.concat_map
                       (fun (constructor : Typed_core.constructor) ->
                         List.mapi
                           (fun index field_sort ->
                             let selected =
                               app (typed_selector constructor index) [ term ]
                             in
                             let recognized =
                               app (typed_recognizer constructor) [ term ]
                             in
                             collect (sort_name :: visited)
                               (string_of_int index
                              :: constructor.symbol.display :: segments)
                               (recognized :: guards) selected field_sort)
                           constructor.arguments)
                  |> List.fold_left
                       (fun result paths ->
                         match (result, paths) with
                         | Ok result, Ok paths -> Ok (result @ paths)
                         | Error error, _ | _, Error error -> Error error)
                       (Ok []))
        | S_int | S_bool | S_unit | S_var _ -> Ok [])
  in
  collect [] [] [] result result_sort

let use_returned_reference_theory generic_calls registry sort =
  let rec visit visited sort =
    match reference_content_sort sort with
    | Some _ -> ()
    | None -> (
        match sort with
        | Typed_core.S_tuple sorts -> List.iter (visit visited) sorts
        | S_app _ ->
            let name = typed_smt_sort sort in
            if not (List.mem name visited) then
              registry.Typed_core.datatypes
              |> List.find_opt (fun (datatype : Typed_core.datatype) ->
                  typed_smt_sort datatype.owner = name)
              |> Option.iter (fun (datatype : Typed_core.datatype) ->
                  List.iter
                    (fun (constructor : Typed_core.constructor) ->
                      use_theory_symbol generic_calls constructor.symbol.key;
                      List.iter (visit (name :: visited)) constructor.arguments)
                    datatype.constructors)
        | S_int | S_bool | S_unit | S_var _ -> ())
  in
  visit [] sort

let typed_initial_reference_state ?registry function_def =
  let sorts = typed_function_reference_sorts ?registry function_def in
  List.map (fun sort -> (heap_key sort, initial_heap_name sort)) sorts

let typed_outcome_payload_sorts ?program expression =
  let rec collect visited outcomes (expression : Typed_core.expr) =
    match expression.desc with
    | Raise (symbol, payload) ->
        ( `Raised,
          symbol.display,
          Option.map (fun value -> value.Typed_core.sort) payload )
        :: Option.fold ~none:outcomes ~some:(collect visited outcomes) payload
    | Perform (symbol, payload) ->
        ( `Performed,
          symbol.display,
          Option.map (fun value -> value.Typed_core.sort) payload )
        :: Option.fold ~none:outcomes ~some:(collect visited outcomes) payload
    | Let (_, value, body) | Sequence (value, body) ->
        collect visited (collect visited outcomes value) body
    | Let_ref (_, _, initial, body) ->
        collect visited (collect visited outcomes initial) body
    | Ref (_, initial) -> collect visited outcomes initial
    | If (condition, if_true, if_false) ->
        collect visited
          (collect visited (collect visited outcomes condition) if_true)
          if_false
    | Try (body, cases) ->
        List.fold_left
          (fun outcomes (_, handler) -> collect visited outcomes handler)
          (collect visited outcomes body)
          cases
    | Match (body, cases) ->
        List.fold_left
          (fun outcomes (_, handler) -> collect visited outcomes handler)
          (collect visited outcomes body)
          cases
    | Handle (body, handlers) ->
        let rec collect_action outcomes = function
          | Typed_core.Abort handler | Typed_core.Resume handler ->
              collect visited outcomes handler
          | Typed_core.Conditional (condition, if_true, if_false) ->
              collect_action
                (collect_action (collect visited outcomes condition) if_true)
                if_false
        in
        List.fold_left
          (fun outcomes (_, _, action) -> collect_action outcomes action)
          (collect visited outcomes body)
          handlers
    | Apply (symbol, expressions) -> (
        let outcomes = List.fold_left (collect visited) outcomes expressions in
        match program with
        | Some (program : Typed_core.program)
          when not (List.mem symbol.key visited) -> (
            match
              List.find_opt
                (fun (callee : Typed_core.function_def) ->
                  callee.symbol.key = symbol.key)
                program.functions
            with
            | Some callee ->
                collect (symbol.key :: visited) outcomes callee.body
            | None -> outcomes)
        | None | Some _ -> outcomes)
    | Tuple expressions
    | Construct (_, expressions)
    | Choose expressions
    | Record (_, expressions) ->
        List.fold_left (collect visited) outcomes expressions
    | Assign (_, value) | Field (_, _, value) -> collect visited outcomes value
    | Var _ | Int _ | Bool _ | Deref _ -> outcomes
  in
  collect [] [] expression |> List.sort_uniq compare

let typed_relational_expr program analysis mode function_def ~initial_state env
    expression =
  let module R = Relational_outcome in
  let choices = ref [] in
  let generic_calls = new_generic_call_state () in
  let continuations = Hashtbl.create 8 in
  let continuation_counter = ref 0 in
  let allocated_references =
    ref
      (typed_reference_arguments function_def
      |> List.filter_map (fun (_, key, sort) ->
          Option.map (fun value -> (value.term, sort)) (List.assoc_opt key env))
      )
  in
  let rec translate env state path (expression : Typed_core.expr) continuation =
    match expression.desc with
    | Raise (exception_, None) -> R.raise_ ~state exception_.display
    | Raise (exception_, Some payload) ->
        translate env state path payload (fun payload state ->
            R.raise_ ~state ~payload exception_.display)
    | Perform (operation, payload) -> (
        let perform payload state =
          let id = "continuation_" ^ string_of_int !continuation_counter in
          incr continuation_counter;
          Hashtbl.add continuations id continuation;
          R.perform ?payload ~state ~operation:operation.display
            ~continuation:id ()
        in
        match payload with
        | None -> perform None state
        | Some payload ->
            translate env state path payload (fun payload state ->
                perform (Some payload) state))
    | Apply (symbol, arguments) -> (
        match
          List.find_opt
            (fun (callee : Typed_core.function_def) ->
              callee.symbol.key = symbol.key
              && (typed_has_exception callee.body
                 || reference_content_sort callee.result <> None
                 || sort_reaches_reference program.Typed_core.registry
                      callee.result
                 || List.exists
                      (fun (contract : Typed_core.contract) ->
                        contract.result_references <> [])
                      callee.contracts))
            program.Typed_core.functions
        with
        | None ->
            let value =
              typed_expr_smt_with_choices program analysis mode function_def
                path [] choices generic_calls env expression
            in
            continuation value.term state
        | Some callee ->
            let recursive =
              Function_analysis.is_recursive_edge analysis
                ~caller:function_def.symbol.key ~callee:callee.symbol.key
            in
            if List.length arguments <> List.length callee.arguments then
              typed_error_at expression.loc
                "effectful call `%s` has unsupported partial arity"
                symbol.display;
            if List.exists typed_has_exception arguments then
              typed_error_at expression.loc
                "effectful call arguments must be evaluated before the call";
            let callee =
              instantiate_function_at_call ~loc:expression.loc callee arguments
                expression.sort
            in
            let termination_condition terms =
              if not recursive then "true"
              else
                let callee_measure =
                  match callee.measure with
                  | Some measure -> measure
                  | None ->
                      typed_error_at expression.loc
                        "recursive outcome callee `%s` needs [@refined.measure]"
                        symbol.display
                in
                let caller_measure =
                  match function_def.Typed_core.measure with
                  | Some measure -> measure
                  | None ->
                      typed_error_at expression.loc
                        "recursive outcome caller `%s` needs [@refined.measure]"
                        function_def.symbol.display
                in
                let callee_term =
                  List.find_map
                    (fun (((formal : Typed_core.symbol), _), term) ->
                      if formal.key = callee_measure.key then Some term
                      else None)
                    (List.combine callee.arguments terms)
                  |> Option.get
                in
                let caller_term =
                  match List.assoc_opt caller_measure.key env with
                  | Some value -> value.term
                  | None -> assert false
                in
                and_
                  [
                    app ">=" [ caller_term; "0" ];
                    app "<" [ callee_term; caller_term ];
                  ]
            in
            if mode = Under then (
              let contracts =
                List.filter
                  (fun (contract : Typed_core.contract) ->
                    contract.mode = Under)
                  callee.contracts
              in
              let summary =
                match contracts with
                | [ summary ] -> summary
                | [] ->
                    typed_error_at expression.loc
                      "effectful under-call `%s` needs one coverage summary"
                      symbol.display
                | _ ->
                    typed_error_at expression.loc
                      "effectful under-call `%s` has ambiguous summaries"
                      symbol.display
              in
              let values =
                List.map
                  (fun argument ->
                    typed_expr_smt_with_choices program analysis Under
                      function_def path [] choices generic_calls env argument)
                  arguments
              in
              let terms = List.map (fun value -> value.term) values in
              let termination = termination_condition terms in
              let call_formula_env =
                List.map2
                  (fun ((formal : Typed_core.symbol), sort) term ->
                    (formal.display, (term, sort)))
                  callee.arguments terms
              in
              let value_formals =
                List.combine callee.arguments terms
                |> List.filter_map
                     (fun (((formal : Typed_core.symbol), sort), term) ->
                       match reference_content_sort sort with
                       | Some _ -> None
                       | None -> Some ((formal.display, sort), term))
              in
              let formals = List.map fst value_formals in
              let value_terms = List.map snd value_formals in
              let complete witnesses =
                List.sort String.compare (List.map fst witnesses)
                = List.sort String.compare (List.map fst formals)
              in
              let parse text =
                parse_formula ~filename:summary.loc.file
                  ~loc:(location_of_span summary.loc)
                  text
              in
              let fresh prefix sort =
                let name = prefix ^ string_of_int (List.length !choices) in
                choices := (name, sort) :: !choices;
                name
              in
              let fresh_ghosts prefix =
                List.map
                  (fun (name, sort) ->
                    ( name,
                      (fresh (prefix ^ smt_identifier name ^ "_") sort, sort) ))
                  summary.ghosts
              in
              let equations target_env witnesses =
                if witnesses = [] then []
                else
                  List.map2
                    (fun (name, sort) actual ->
                      let witness = parse (List.assoc name witnesses) in
                      formula_theory_symbols ~expected:sort program.registry
                        target_env witness
                      |> List.iter (use_theory_symbol generic_calls);
                      app "="
                        [
                          actual;
                          typed_formula ~expected:sort program.registry
                            target_env witness;
                        ])
                    formals value_terms
              in
              let reference_formals = typed_reference_arguments callee in
              let actual_cell name =
                let _, _, sort =
                  match
                    List.find_opt
                      (fun (formal, _, _) -> formal = name)
                      reference_formals
                  with
                  | Some formal -> formal
                  | None ->
                      typed_error_at expression.loc
                        "state summary `%s` is not a reference parameter" name
                in
                let index =
                  List.find_mapi
                    (fun index ((formal : Typed_core.symbol), _) ->
                      if formal.display = name then Some index else None)
                    callee.arguments
                  |> Option.get
                in
                (List.nth terms index, sort)
              in
              let old_reference_env =
                List.map
                  (fun (name, _, sort) ->
                    let actual, _ = actual_cell name in
                    ("old_" ^ name, (heap_select state actual sort, sort)))
                  reference_formals
              in
              List.iter
                (fun name ->
                  let _ = actual_cell name in
                  if not (List.mem_assoc name summary.state) then
                    typed_error_at expression.loc
                      "coverage modifies `%s` needs a state target predicate"
                      name)
                summary.modifies;
              let relation_guard relation relation_env =
                match relation with
                | None -> []
                | Some relation ->
                    let relation = parse relation in
                    formula_theory_symbols program.registry relation_env
                      relation
                    |> List.iter (use_theory_symbol generic_calls);
                    [ typed_formula program.registry relation_env relation ]
              in
              let paths = ref [] in
              if
                summary.witnesses <> []
                || summary.witness_relation <> None
                || formals = []
                   && summary.state_witnesses <> []
                   && summary.ghosts = []
              then (
                if summary.witnesses <> [] && not (complete summary.witnesses)
                then
                  typed_error_at expression.loc
                    "normal coverage summary for `%s` has incomplete witnesses"
                    symbol.display;
                if
                  reference_formals <> []
                  && summary.state_witnesses = []
                  && summary.witness_relation = None
                then
                  typed_error_at expression.loc
                    "normal coverage summary for `%s` needs state_witnesses or \
                     witness_relation"
                    symbol.display;
                let result = fresh "call_result_" callee.result in
                let ( result_target,
                      result_state_guards,
                      result_final_state,
                      result_updates ) =
                  match reference_content_sort callee.result with
                  | None ->
                      if summary.result_state <> None || summary.result_fresh
                      then
                        typed_error_at expression.loc
                          "non-reference coverage summary declares result state";
                      (None, [], state, [])
                  | Some content_sort ->
                      let predicate =
                        match summary.result_state with
                        | Some predicate -> parse predicate
                        | None ->
                            typed_error_at expression.loc
                              "reference-returning coverage summary `%s` needs \
                               result_state"
                              symbol.display
                      in
                      let content = fresh "call_result_state_" content_sort in
                      let freshness =
                        if not summary.result_fresh then []
                        else
                          let existing =
                            !allocated_references
                            |> List.filter_map (fun (identity, sort) ->
                                if
                                  typed_smt_sort sort
                                  = typed_smt_sort content_sort
                                then Some identity
                                else None)
                          in
                          match existing with
                          | [] -> []
                          | existing -> [ app "distinct" (result :: existing) ]
                      in
                      allocated_references :=
                        (result, content_sort) :: !allocated_references;
                      ( Some (content_sort, content, predicate),
                        freshness,
                        heap_store state result content_sort content,
                        [ (result, content_sort, content) ] )
                in
                let owned_paths =
                  if reference_content_sort callee.result <> None then []
                  else
                    match
                      returned_reference_paths program.registry
                        ~result_sort:callee.result ~result
                    with
                    | Ok paths -> paths
                    | Error path ->
                        typed_error_at expression.loc
                          "recursive reachable-reference path `%s` needs an \
                           ownership invariant"
                          path
                in
                if owned_paths <> [] then
                  use_returned_reference_theory generic_calls program.registry
                    callee.result;
                if
                  List.sort String.compare
                    (List.map (fun path -> path.path) owned_paths)
                  <> List.sort String.compare
                       (List.map fst summary.result_references)
                then
                  typed_error_at expression.loc
                    "reference-containing coverage summary has incomplete \
                     result_references";
                let ( owned_targets,
                      owned_freshness,
                      owned_final_state,
                      owned_updates ) =
                  List.fold_left
                    (fun (targets, guards, final_state, updates) path ->
                      let content =
                        fresh "call_reachable_state_" path.content_sort
                      in
                      let freshness =
                        if
                          not
                            (List.mem path.path summary.result_fresh_references)
                        then []
                        else
                          let existing =
                            !allocated_references
                            |> List.filter_map (fun (identity, sort) ->
                                if
                                  typed_smt_sort sort
                                  = typed_smt_sort path.content_sort
                                then Some identity
                                else None)
                          in
                          match existing with
                          | [] -> []
                          | existing ->
                              [
                                app "=>"
                                  [
                                    path.guard;
                                    app "distinct" (path.identity :: existing);
                                  ];
                              ]
                      in
                      allocated_references :=
                        (path.identity, path.content_sort)
                        :: !allocated_references;
                      ( ( path,
                          content,
                          parse (List.assoc path.path summary.result_references)
                        )
                        :: targets,
                        freshness @ guards,
                        heap_store_guarded final_state path.guard path.identity
                          path.content_sort content,
                        (path.identity, path.content_sort, content, path.guard)
                        :: updates ))
                    ([], [], result_final_state, [])
                    owned_paths
                in
                let state_targets =
                  List.map
                    (fun (name, predicate) ->
                      let _, _, sort =
                        List.find
                          (fun (formal, _, _) -> formal = name)
                          reference_formals
                      in
                      let actual, _ = actual_cell name in
                      (name, actual, sort, fresh "call_state_" sort, predicate))
                    summary.state
                in
                let public_target_env =
                  ("result", (result, callee.result))
                  :: Option.fold ~none:[]
                       ~some:(fun (sort, content, _predicate) ->
                         [ ("result_value", (content, sort)) ])
                       result_target
                  @ List.map
                      (fun (path, content, _predicate) ->
                        ( returned_reference_value_name path.path,
                          (content, path.content_sort) ))
                      owned_targets
                  @ List.map
                      (fun (name, _, sort, target, _) -> (name, (target, sort)))
                      state_targets
                in
                let ghost_env = fresh_ghosts "call_ghost_" in
                let witness_env = ghost_env @ public_target_env in
                let relation_env =
                  witness_env @ call_formula_env @ old_reference_env
                in
                let post = parse summary.post in
                formula_theory_symbols program.registry public_target_env post
                |> List.iter (use_theory_symbol generic_calls);
                let result_state_guards =
                  match result_target with
                  | None -> result_state_guards
                  | Some (sort, content, predicate) ->
                      let state_env =
                        ("value", (content, sort)) :: public_target_env
                      in
                      formula_theory_symbols program.registry state_env
                        predicate
                      |> List.iter (use_theory_symbol generic_calls);
                      typed_formula program.registry state_env predicate
                      :: result_state_guards
                in
                let owned_state_guards =
                  List.map
                    (fun (path, content, predicate) ->
                      let state_env =
                        ("value", (content, path.content_sort))
                        :: public_target_env
                      in
                      formula_theory_symbols program.registry state_env
                        predicate
                      |> List.iter (use_theory_symbol generic_calls);
                      app "=>"
                        [
                          path.guard;
                          typed_formula program.registry state_env predicate;
                        ])
                    owned_targets
                in
                let state_witness_guards =
                  if reference_formals = [] then []
                  else (
                    if
                      List.sort String.compare
                        (List.map (fun (name, _, _) -> name) reference_formals)
                      <> List.sort String.compare
                           (List.map fst summary.state_witnesses)
                    then
                      if summary.state_witnesses <> [] then
                        typed_error_at expression.loc
                          "under state summary has incomplete state_witnesses";
                    if summary.state_witnesses = [] then []
                    else
                      List.map
                        (fun (name, _, sort) ->
                          let actual, _ = actual_cell name in
                          let old = heap_select state actual sort in
                          let witness =
                            parse (List.assoc name summary.state_witnesses)
                          in
                          app "="
                            [
                              old;
                              typed_formula ~expected:sort program.registry
                                witness_env witness;
                            ])
                        reference_formals)
                in
                let state_post_guards, final_state, state_updates =
                  List.fold_left
                    (fun (guards, final_state, updates)
                         (_name, actual, sort, target, predicate) ->
                      let old = heap_select state actual sort in
                      let predicate = parse predicate in
                      let state_env =
                        ("value", (target, sort))
                        :: ("old", (old, sort))
                        :: public_target_env
                      in
                      ( typed_formula program.registry state_env predicate
                        :: guards,
                        heap_store final_state actual sort target,
                        (actual, sort, target) :: updates ))
                    ( owned_state_guards @ owned_freshness @ result_state_guards,
                      owned_final_state,
                      result_updates )
                    state_targets
                in
                let alias_guards =
                  guarded_alias_consistency
                    (List.map
                       (fun (identity, sort, value) ->
                         (identity, sort, value, "true"))
                       state_updates
                    @ owned_updates)
                in
                paths :=
                  Relational_outcome.
                    {
                      guard =
                        and_
                          (termination
                           :: typed_formula program.registry public_target_env
                                post
                           :: equations witness_env summary.witnesses
                          @ state_witness_guards @ state_post_guards
                          @ alias_guards
                          @ relation_guard summary.witness_relation relation_env
                          );
                      initial_state = state;
                      final_state;
                      outcome = Return result;
                    }
                  :: !paths);
              let payloads = typed_outcome_payload_sorts callee.body in
              let payload_sort kind name =
                let rec find = function
                  | [] -> None
                  | (candidate, candidate_name, sort) :: rest ->
                      if candidate = kind && candidate_name = name then sort
                      else find rest
                in
                find payloads
              in
              let continuation_id =
                "continuation_" ^ string_of_int !continuation_counter
              in
              incr continuation_counter;
              Hashtbl.add continuations continuation_id continuation;
              List.iter
                (fun (outcome : Typed_core.coverage_outcome) ->
                  List.iter
                    (fun (kind, name, cell) ->
                      if kind = outcome.kind && name = outcome.name then
                        let _ = actual_cell cell in
                        if
                          not
                            (List.exists
                               (fun (state_kind, state_name, state_cell, _) ->
                                 state_kind = kind && state_name = name
                                 && state_cell = cell)
                               summary.outcome_state)
                        then
                          typed_error_at expression.loc
                            "coverage outcome modifies `%s` needs a state \
                             target predicate"
                            cell)
                    summary.outcome_modifies;
                  if outcome.witnesses <> [] && not (complete outcome.witnesses)
                  then
                    typed_error_at expression.loc
                      "coverage outcome `%s` has incomplete witnesses"
                      outcome.name;
                  if outcome.witnesses = [] && outcome.witness_relation = None
                  then
                    typed_error_at expression.loc
                      "coverage outcome `%s` needs witnesses or \
                       witness_relation"
                      outcome.name;
                  if
                    reference_formals <> []
                    && summary.state_witnesses = []
                    && outcome.witness_relation = None
                  then
                    typed_error_at expression.loc
                      "coverage outcome `%s` needs state_witnesses or \
                       witness_relation"
                      outcome.name;
                  let kind, sort =
                    match outcome.kind with
                    | "raise" -> (`Raised, payload_sort `Raised outcome.name)
                    | "perform" ->
                        (`Performed, payload_sort `Performed outcome.name)
                    | kind ->
                        typed_error_at expression.loc
                          "unknown coverage outcome kind `%s`" kind
                  in
                  let payload = Option.map (fresh "call_payload_") sort in
                  let payload_env =
                    match (sort, payload) with
                    | Some sort, Some payload ->
                        [ ("payload", (payload, sort)) ]
                    | _ -> []
                  in
                  let state_targets =
                    summary.outcome_state
                    |> List.filter_map (fun (kind, name, cell, predicate) ->
                        if kind <> outcome.kind || name <> outcome.name then
                          None
                        else
                          let actual, sort = actual_cell cell in
                          Some
                            ( cell,
                              actual,
                              sort,
                              fresh "call_outcome_state_" sort,
                              predicate ))
                  in
                  let public_target_env =
                    List.map
                      (fun (name, _, sort, target, _) -> (name, (target, sort)))
                      state_targets
                    @ payload_env
                  in
                  let ghost_env = fresh_ghosts "call_outcome_ghost_" in
                  let witness_env = ghost_env @ public_target_env in
                  let relation_env =
                    witness_env @ call_formula_env @ old_reference_env
                  in
                  let post = parse outcome.post in
                  formula_theory_symbols program.registry public_target_env post
                  |> List.iter (use_theory_symbol generic_calls);
                  let state_witness_guards =
                    if reference_formals = [] then []
                    else (
                      if
                        List.sort String.compare
                          (List.map
                             (fun (name, _, _) -> name)
                             reference_formals)
                        <> List.sort String.compare
                             (List.map fst summary.state_witnesses)
                      then
                        if summary.state_witnesses <> [] then
                          typed_error_at expression.loc
                            "under outcome summary has incomplete \
                             state_witnesses";
                      if summary.state_witnesses = [] then []
                      else
                        List.map
                          (fun (name, _, sort) ->
                            let actual, _ = actual_cell name in
                            let old = heap_select state actual sort in
                            let witness =
                              parse (List.assoc name summary.state_witnesses)
                            in
                            app "="
                              [
                                old;
                                typed_formula ~expected:sort program.registry
                                  witness_env witness;
                              ])
                          reference_formals)
                  in
                  let state_post_guards, final_state =
                    List.fold_left
                      (fun (guards, final_state)
                           (_name, actual, sort, target, predicate) ->
                        let old = heap_select state actual sort in
                        let predicate = parse predicate in
                        let state_env =
                          ("value", (target, sort))
                          :: ("old", (old, sort))
                          :: public_target_env
                        in
                        formula_theory_symbols program.registry state_env
                          predicate
                        |> List.iter (use_theory_symbol generic_calls);
                        ( typed_formula program.registry state_env predicate
                          :: guards,
                          heap_store final_state actual sort target ))
                      ([], state) state_targets
                  in
                  let alias_guards =
                    state_targets
                    |> List.map
                         (fun (_name, actual, sort, target, _predicate) ->
                           (actual, sort, target))
                    |> alias_consistency
                  in
                  let guard =
                    and_
                      (termination
                       :: typed_formula program.registry public_target_env post
                       :: equations witness_env outcome.witnesses
                      @ state_witness_guards @ state_post_guards @ alias_guards
                      @ relation_guard outcome.witness_relation relation_env)
                  in
                  let path =
                    match kind with
                    | `Raised ->
                        Relational_outcome.
                          {
                            guard;
                            initial_state = state;
                            final_state;
                            outcome =
                              Raised { exception_ = outcome.name; payload };
                          }
                    | `Performed ->
                        Relational_outcome.
                          {
                            guard;
                            initial_state = state;
                            final_state;
                            outcome =
                              Performed
                                {
                                  operation = outcome.name;
                                  payload;
                                  continuation = Some continuation_id;
                                };
                          }
                  in
                  paths := path :: !paths)
                summary.outcomes;
              if !paths = [] then
                typed_error_at expression.loc
                  "effectful under-call `%s` has no constructive outcome"
                  symbol.display;
              R.bind (List.rev !paths) continuation)
            else
              let contracts =
                List.filter
                  (fun (contract : Typed_core.contract) -> contract.mode = Over)
                  callee.contracts
              in
              let summary =
                match contracts with
                | [ summary ] -> summary
                | [] ->
                    typed_error_at expression.loc
                      "effectful call `%s` needs one safety outcome summary"
                      symbol.display
                | _ ->
                    typed_error_at expression.loc
                      "effectful call `%s` has ambiguous safety summaries"
                      symbol.display
              in
              let values =
                List.map
                  (fun argument ->
                    typed_expr_smt_with_choices program analysis mode
                      function_def path [] choices generic_calls env argument)
                  arguments
              in
              let terms = List.map (fun value -> value.term) values in
              let termination = termination_condition terms in
              let formula_env =
                List.map2
                  (fun ((formal : Typed_core.symbol), sort) term ->
                    (formal.display, (term, sort)))
                  callee.arguments terms
              in
              let parse text =
                parse_formula ~filename:summary.loc.file
                  ~loc:(location_of_span summary.loc)
                  text
              in
              let mark env formula =
                formula_theory_symbols program.registry env formula
                |> List.iter (use_theory_symbol generic_calls)
              in
              let pre_formula = parse summary.pre in
              mark formula_env pre_formula;
              generic_calls.side_conditions <-
                under_path path
                  (typed_formula program.registry formula_env pre_formula)
                :: generic_calls.side_conditions;
              let reference_formals = typed_reference_arguments callee in
              let actual_cell name =
                let _, _, sort =
                  match
                    List.find_opt
                      (fun (formal, _, _) -> formal = name)
                      reference_formals
                  with
                  | None ->
                      typed_error_at expression.loc
                        "state summary `%s` is not a reference parameter" name
                  | Some formal -> formal
                in
                let index =
                  List.find_mapi
                    (fun index ((formal : Typed_core.symbol), _) ->
                      if formal.display = name then Some index else None)
                    callee.arguments
                  |> Option.get
                in
                (List.nth terms index, sort)
              in
              List.iter
                (fun (name, predicate) ->
                  let actual, sort = actual_cell name in
                  let old = heap_select state actual sort in
                  let predicate = parse predicate in
                  let state_env = ("value", (old, sort)) :: formula_env in
                  mark state_env predicate;
                  generic_calls.side_conditions <-
                    under_path path
                      (typed_formula program.registry state_env predicate)
                    :: generic_calls.side_conditions)
                summary.requires_state;
              if recursive then
                generic_calls.side_conditions <-
                  under_path path termination :: generic_calls.side_conditions;
              let fresh prefix sort =
                let name = prefix ^ string_of_int (List.length !choices) in
                choices := (name, sort) :: !choices;
                name
              in
              let result = fresh "call_result_" callee.result in
              let result_env =
                ("result", (result, callee.result)) :: formula_env
              in
              let post_formula = parse summary.post in
              mark result_env post_formula;
              let result_state_guards, result_final_state, result_updates =
                match reference_content_sort callee.result with
                | None ->
                    if summary.result_state <> None || summary.result_fresh then
                      typed_error_at expression.loc
                        "non-reference summary declares escaping result state";
                    ([], state, [])
                | Some content_sort ->
                    let predicate =
                      match summary.result_state with
                      | Some predicate -> parse predicate
                      | None ->
                          typed_error_at expression.loc
                            "reference-returning summary `%s` needs \
                             result_state"
                            symbol.display
                    in
                    let content = fresh "call_result_state_" content_sort in
                    let state_env =
                      ("value", (content, content_sort)) :: result_env
                    in
                    mark state_env predicate;
                    let freshness =
                      if not summary.result_fresh then []
                      else
                        let existing =
                          !allocated_references
                          |> List.filter_map (fun (identity, sort) ->
                              if
                                typed_smt_sort sort
                                = typed_smt_sort content_sort
                              then Some identity
                              else None)
                        in
                        match existing with
                        | [] -> []
                        | existing -> [ app "distinct" (result :: existing) ]
                    in
                    allocated_references :=
                      (result, content_sort) :: !allocated_references;
                    ( typed_formula program.registry state_env predicate
                      :: freshness,
                      heap_store state result content_sort content,
                      [ (result, content_sort, content) ] )
              in
              let owned_paths =
                if reference_content_sort callee.result <> None then []
                else
                  match
                    returned_reference_paths program.registry
                      ~result_sort:callee.result ~result
                  with
                  | Ok paths -> paths
                  | Error path ->
                      typed_error_at expression.loc
                        "recursive reachable-reference path `%s` needs an \
                         ownership invariant"
                        path
              in
              if owned_paths <> [] then
                use_returned_reference_theory generic_calls program.registry
                  callee.result;
              let expected_paths =
                List.map (fun path -> path.path) owned_paths
              in
              if
                List.sort String.compare expected_paths
                <> List.sort String.compare
                     (List.map fst summary.result_references)
              then
                typed_error_at expression.loc
                  "reference-containing result summary has incomplete \
                   result_references";
              let owned_guards, owned_final_state, owned_updates =
                List.fold_left
                  (fun (guards, final_state, updates) path ->
                    let predicate =
                      parse (List.assoc path.path summary.result_references)
                    in
                    let content =
                      fresh "call_reachable_state_" path.content_sort
                    in
                    let state_env =
                      ("value", (content, path.content_sort)) :: result_env
                    in
                    mark state_env predicate;
                    let predicate =
                      app "=>"
                        [
                          path.guard;
                          typed_formula program.registry state_env predicate;
                        ]
                    in
                    let freshness =
                      if
                        not (List.mem path.path summary.result_fresh_references)
                      then []
                      else
                        let existing =
                          !allocated_references
                          |> List.filter_map (fun (identity, sort) ->
                              if
                                typed_smt_sort sort
                                = typed_smt_sort path.content_sort
                              then Some identity
                              else None)
                        in
                        match existing with
                        | [] -> []
                        | existing ->
                            [
                              app "=>"
                                [
                                  path.guard;
                                  app "distinct" (path.identity :: existing);
                                ];
                            ]
                    in
                    allocated_references :=
                      (path.identity, path.content_sort)
                      :: !allocated_references;
                    ( (predicate :: freshness) @ guards,
                      heap_store_guarded final_state path.guard path.identity
                        path.content_sort content,
                      (path.identity, path.content_sort, content, path.guard)
                      :: updates ))
                  (result_state_guards, result_final_state, [])
                  owned_paths
              in
              let normal_state_clauses =
                summary.state
                @ List.filter_map
                    (fun name ->
                      let _ = actual_cell name in
                      if List.mem_assoc name summary.state then None
                      else Some (name, "true"))
                    summary.modifies
              in
              let state_guards, final_state, state_updates =
                List.fold_left
                  (fun (guards, final_state, updates) (name, predicate) ->
                    let actual, sort = actual_cell name in
                    let old = heap_select state actual sort in
                    let value = fresh "call_state_" sort in
                    let predicate = parse predicate in
                    let state_env =
                      ("value", (value, sort))
                      :: ("old", (old, sort))
                      :: result_env
                    in
                    mark state_env predicate;
                    ( typed_formula program.registry state_env predicate
                      :: guards,
                      heap_store final_state actual sort value,
                      (actual, sort, value) :: updates ))
                  (owned_guards, owned_final_state, result_updates)
                  normal_state_clauses
              in
              let state_guards =
                guarded_alias_consistency
                  (List.map
                     (fun (identity, sort, value) ->
                       (identity, sort, value, "true"))
                     state_updates
                  @ owned_updates)
                @ state_guards
              in
              let normal =
                Relational_outcome.
                  {
                    guard =
                      and_
                        (typed_formula program.registry result_env post_formula
                        :: state_guards);
                    initial_state = state;
                    final_state;
                    outcome = Return result;
                  }
              in
              let payloads = typed_outcome_payload_sorts callee.body in
              let payload_sort kind name =
                let rec find = function
                  | [] -> None
                  | (candidate, candidate_name, sort) :: rest ->
                      if candidate = kind && candidate_name = name then sort
                      else find rest
                in
                find payloads
              in
              let outcome_state kind outcome target_env =
                let guards, final_state, updates =
                  let clauses =
                    summary.outcome_state
                    |> List.filter (fun (candidate_kind, candidate, _, _) ->
                        candidate_kind = kind && candidate = outcome)
                  in
                  let clauses =
                    clauses
                    @ List.filter_map
                        (fun (candidate_kind, candidate, name) ->
                          if candidate_kind <> kind || candidate <> outcome then
                            None
                          else
                            let _ = actual_cell name in
                            if
                              List.exists
                                (fun (_, _, existing, _) -> existing = name)
                                clauses
                            then None
                            else Some (kind, outcome, name, "true"))
                        summary.outcome_modifies
                  in
                  clauses
                  |> List.fold_left
                       (fun (guards, final_state, updates)
                            (_kind, _outcome, name, predicate) ->
                         let actual, sort = actual_cell name in
                         let old = heap_select state actual sort in
                         let value = fresh "call_outcome_state_" sort in
                         let predicate = parse predicate in
                         let state_env =
                           ("value", (value, sort))
                           :: ("old", (old, sort))
                           :: target_env
                         in
                         mark state_env predicate;
                         ( typed_formula program.registry state_env predicate
                           :: guards,
                           heap_store final_state actual sort value,
                           (actual, sort, value) :: updates ))
                       ([], state, [])
                in
                (alias_consistency updates @ guards, final_state)
              in
              let exceptional =
                List.map
                  (fun (name, predicate) ->
                    let sort = payload_sort `Raised name in
                    let payload = Option.map (fresh "call_exception_") sort in
                    let env =
                      match (sort, payload) with
                      | Some sort, Some payload ->
                          ("payload", (payload, sort)) :: formula_env
                      | _ -> formula_env
                    in
                    let predicate = parse predicate in
                    mark env predicate;
                    let state_guards, final_state =
                      outcome_state "raise" name env
                    in
                    Relational_outcome.
                      {
                        guard =
                          and_
                            (typed_formula program.registry env predicate
                            :: state_guards);
                        initial_state = state;
                        final_state;
                        outcome = Raised { exception_ = name; payload };
                      })
                  summary.raises
              in
              let continuation_id =
                "continuation_" ^ string_of_int !continuation_counter
              in
              incr continuation_counter;
              Hashtbl.add continuations continuation_id continuation;
              let performed =
                List.map
                  (fun (name, predicate) ->
                    let sort = payload_sort `Performed name in
                    let payload = Option.map (fresh "call_effect_") sort in
                    let env =
                      match (sort, payload) with
                      | Some sort, Some payload ->
                          ("payload", (payload, sort)) :: formula_env
                      | _ -> formula_env
                    in
                    let predicate = parse predicate in
                    mark env predicate;
                    let state_guards, final_state =
                      outcome_state "perform" name env
                    in
                    Relational_outcome.
                      {
                        guard =
                          and_
                            (typed_formula program.registry env predicate
                            :: state_guards);
                        initial_state = state;
                        final_state;
                        outcome =
                          Performed
                            {
                              operation = name;
                              payload;
                              continuation = Some continuation_id;
                            };
                      })
                  summary.performs
              in
              R.bind ((normal :: exceptional) @ performed) continuation)
    | Choose [ left; right ] ->
        translate env state path left continuation
        @ translate env state path right continuation
    | Choose _ ->
        typed_error_at expression.loc
          "the relational choose primitive requires exactly two alternatives"
    | Handle (body, handlers) ->
        let boundary value state = R.return ~state value in
        let rec discharge relation =
          List.fold_left
            (fun relation (operation, payload_binder, action) ->
              R.handle_effect ~operation:operation.Typed_core.display relation
                (fun ~payload ~continuation ~state ->
                  let continuation_id =
                    match continuation with
                    | Some id -> id
                    | None ->
                        typed_error_at expression.loc
                          "effect handler received no continuation"
                  in
                  let handler_env =
                    match (payload_binder, payload) with
                    | Some (binder : Typed_core.symbol), Some payload ->
                        (binder.key, { term = payload; refinement = None })
                        :: env
                    | None, _ -> env
                    | Some _, None ->
                        typed_error_at expression.loc
                          "effect handler expected a payload"
                  in
                  let captured =
                    match Hashtbl.find_opt continuations continuation_id with
                    | Some continuation -> continuation
                    | None ->
                        typed_error_at expression.loc
                          "effect continuation escaped its handler"
                  in
                  let rec execute state path = function
                    | Typed_core.Abort handler ->
                        translate handler_env state path handler boundary
                    | Typed_core.Resume value ->
                        translate handler_env state path value captured
                    | Typed_core.Conditional (condition, if_true, if_false) ->
                        if typed_has_exception condition then
                          typed_error_at condition.loc
                            "effectful continuation conditions are unsupported";
                        let condition =
                          typed_expr_smt_with_choices program analysis mode
                            function_def path [] choices generic_calls
                            handler_env condition
                        in
                        R.branch ~condition:condition.term
                          ~if_true:
                            (execute state (condition.term :: path) if_true)
                          ~if_false:
                            (execute state
                               (app "not" [ condition.term ] :: path)
                               if_false)
                  in
                  let generated = execute state path action in
                  discharge generated))
            relation handlers
        in
        R.bind (discharge (translate env state path body boundary)) continuation
    | If (condition, if_true, if_false) ->
        if typed_has_exception condition then
          typed_error_at condition.loc
            "exceptionful conditions are not yet supported";
        let condition =
          typed_expr_smt_with_choices program analysis mode function_def path []
            choices generic_calls env condition
        in
        R.branch ~condition:condition.term
          ~if_true:
            (translate env state (condition.term :: path) if_true continuation)
          ~if_false:
            (translate env state
               (app "not" [ condition.term ] :: path)
               if_false continuation)
    | Let (symbol, value, body) ->
        translate env state path value (fun value state ->
            translate
              ((symbol.key, { term = value; refinement = None }) :: env)
              state path body continuation)
    | Match (scrutinee, cases) ->
        translate env state path scrutinee (fun value state ->
            let rec branches previous = function
              | [] -> []
              | (pattern, body) :: rest ->
                  use_pattern_theory generic_calls pattern;
                  let guard, case_env = typed_pattern_smt env value pattern in
                  let effective_guard =
                    match previous with
                    | [] -> guard
                    | previous -> and_ [ guard; app "not" [ or_ previous ] ]
                  in
                  R.branch ~condition:effective_guard
                    ~if_true:
                      (translate case_env state (effective_guard :: path) body
                         continuation)
                    ~if_false:[]
                  @ branches (guard :: previous) rest
            in
            branches [] cases)
    | Try (body, cases) ->
        let boundary value state = R.return ~state value in
        let handled =
          R.try_with (translate env state path body boundary)
            (fun ~exception_ ~payload ~state ->
              match
                List.find_opt
                  (fun (pattern, _) ->
                    match pattern with
                    | Typed_core.Exn_any -> true
                    | Exn (symbol, _) -> symbol.display = exception_)
                  cases
              with
              | Some (pattern, handler) ->
                  let handler_env =
                    match (pattern, payload) with
                    | ( Typed_core.Exn (_, Some (binder : Typed_core.symbol)),
                        Some payload ) ->
                        (binder.key, { term = payload; refinement = None })
                        :: env
                    | Exn (_, None), _ | Exn_any, _ -> env
                    | Exn (_, Some _), None ->
                        typed_error_at expression.loc
                          "exception handler expected a payload"
                  in
                  translate handler_env state path handler boundary
              | None -> R.raise_ ~state exception_)
        in
        R.bind handled continuation
    | Ref (sort, initial) ->
        translate env state path initial (fun value state ->
            let identity =
              "ref_alloc_" ^ string_of_int (List.length !choices)
            in
            choices := (identity, reference_sort sort) :: !choices;
            (match
               List.filter_map
                 (fun (existing, existing_sort) ->
                   if typed_smt_sort existing_sort = typed_smt_sort sort then
                     Some existing
                   else None)
                 !allocated_references
             with
            | [] -> ()
            | existing ->
                generic_calls.semantic_assumptions <-
                  app "distinct" (identity :: existing)
                  :: generic_calls.semantic_assumptions);
            allocated_references := (identity, sort) :: !allocated_references;
            let state = heap_store state identity sort value in
            continuation identity state)
    | Let_ref (symbol, sort, initial, body) ->
        translate env state path initial (fun value state ->
            let identity = "ref_" ^ smt_identifier symbol.key in
            choices := (identity, reference_sort sort) :: !choices;
            (match
               List.filter_map
                 (fun (existing, existing_sort) ->
                   if typed_smt_sort existing_sort = typed_smt_sort sort then
                     Some existing
                   else None)
                 !allocated_references
             with
            | [] -> ()
            | existing ->
                generic_calls.semantic_assumptions <-
                  app "distinct" (identity :: existing)
                  :: generic_calls.semantic_assumptions);
            allocated_references := (identity, sort) :: !allocated_references;
            generic_calls.local_initial_values <-
              (identity, value) :: generic_calls.local_initial_values;
            let key = heap_key sort in
            let heap =
              match List.assoc_opt key state with
              | Some heap -> heap
              | None -> initial_heap_name sort
            in
            let state =
              (key, app "store" [ heap; identity; value ])
              :: List.remove_assoc key state
            in
            let env =
              (symbol.key, { term = identity; refinement = None }) :: env
            in
            translate env state path body continuation)
    | Deref symbol ->
        let identity =
          match List.assoc_opt symbol.key env with
          | Some value -> value.term
          | None ->
              typed_error_at expression.loc
                "reference `%s` escaped its identity environment" symbol.display
        in
        let key = heap_key expression.sort in
        let heap =
          match List.assoc_opt key state with
          | Some heap -> heap
          | None ->
              typed_error_at expression.loc
                "reference `%s` has no heap for its content sort" symbol.display
        in
        R.bind (R.return ~state (app "select" [ heap; identity ])) continuation
    | Assign (symbol, value) ->
        let identity =
          match List.assoc_opt symbol.key env with
          | Some value -> value.term
          | None ->
              typed_error_at expression.loc
                "reference `%s` escaped its identity environment" symbol.display
        in
        let sort = value.sort in
        let key = heap_key sort in
        if not (List.mem_assoc key state) then
          typed_error_at expression.loc
            "reference `%s` has no heap for its content sort" symbol.display;
        translate env state path value (fun value state ->
            let heap = List.assoc key state in
            let state =
              (key, app "store" [ heap; identity; value ])
              :: List.remove_assoc key state
            in
            continuation "unit" state)
    | Sequence (first, second) ->
        translate env state path first (fun _ state ->
            translate env state path second continuation)
    | _ ->
        if typed_has_exception expression then
          typed_error_at expression.loc
            "exception is nested in an unsupported evaluation context";
        let value =
          typed_expr_smt_with_choices program analysis mode function_def [] []
            choices generic_calls env expression
        in
        continuation value.term state
  in
  let boundary value state = R.return ~state value in
  let relation =
    translate env initial_state [] expression boundary
    |> List.map (fun (path : R.path) -> { path with initial_state })
  in
  (relation, List.rev !choices, generic_calls)

let typed_collect_sorts program function_def =
  let module Set = Set.Make (String) in
  let rec closed = function
    | Typed_core.S_var _ -> false
    | S_tuple sorts | S_app (_, sorts) -> List.for_all closed sorts
    | S_int | S_bool | S_unit -> true
  in
  let rec add set sort =
    let set = Set.add (typed_smt_sort sort) set in
    match sort with
    | Typed_core.S_tuple sorts | S_app (_, sorts) ->
        List.fold_left add set sorts
    | S_int | S_bool | S_unit | S_var _ -> set
  in
  let set =
    List.fold_left
      (fun set (_, sort) -> add set sort)
      Set.empty function_def.Typed_core.arguments
  in
  let set = add set function_def.result in
  let set =
    List.fold_left
      (fun set sort -> if closed sort then add set sort else set)
      set
      (typed_expression_sorts function_def.body)
  in
  let set =
    List.fold_left
      (fun set (contract : Typed_core.contract) ->
        List.fold_left (fun set (_, sort) -> add set sort) set contract.ghosts)
      set function_def.contracts
  in
  let set =
    List.fold_left
      (fun set sort -> add (add set sort) (reference_sort sort))
      set
      (typed_function_reference_sorts ~registry:program.Typed_core.registry
         function_def)
  in
  let set =
    Hashtbl.fold
      (fun _ (logic_symbol : Typed_core.logic_symbol) set ->
        let set = List.fold_left add set logic_symbol.arguments in
        add set logic_symbol.result)
      program.Typed_core.registry.logic_by_name set
  in
  let set =
    List.fold_left
      (fun set (axiom : Typed_core.axiom) ->
        List.fold_left (fun set (_, sort) -> add set sort) set axiom.variables)
      set program.registry.axioms
  in
  let set =
    List.fold_left
      (fun set (lemma : Typed_core.axiom) ->
        List.fold_left (fun set (_, sort) -> add set sort) set lemma.variables)
      set program.registry.checked_lemmas
  in
  List.fold_left
    (fun set (datatype : Typed_core.datatype) ->
      let set = add set datatype.Typed_core.owner in
      List.fold_left
        (fun set (constructor : Typed_core.constructor) ->
          List.fold_left add set constructor.Typed_core.arguments)
        set datatype.constructors)
    set program.Typed_core.registry.datatypes
  |> Set.elements

let typed_collect_sort_values program function_def =
  let values = Hashtbl.create 32 in
  let rec closed = function
    | Typed_core.S_var _ -> false
    | S_tuple sorts | S_app (_, sorts) -> List.for_all closed sorts
    | S_int | S_bool | S_unit -> true
  in
  let rec add sort =
    Hashtbl.replace values (typed_smt_sort sort) sort;
    match sort with
    | Typed_core.S_tuple sorts | S_app (_, sorts) -> List.iter add sorts
    | S_int | S_bool | S_unit | S_var _ -> ()
  in
  List.iter (fun (_, sort) -> add sort) function_def.Typed_core.arguments;
  add function_def.result;
  List.iter
    (fun sort -> if closed sort then add sort)
    (typed_expression_sorts function_def.body);
  List.iter
    (fun (contract : Typed_core.contract) ->
      List.iter (fun (_, sort) -> add sort) contract.ghosts)
    function_def.contracts;
  List.iter
    (fun sort ->
      add sort;
      add (reference_sort sort))
    (typed_function_reference_sorts ~registry:program.Typed_core.registry
       function_def);
  List.iter
    (fun (datatype : Typed_core.datatype) ->
      add datatype.owner;
      List.iter
        (fun (constructor : Typed_core.constructor) ->
          List.iter add constructor.arguments)
        datatype.constructors)
    program.Typed_core.registry.datatypes;
  Hashtbl.iter
    (fun _ (logic_symbol : Typed_core.logic_symbol) ->
      List.iter add logic_symbol.arguments;
      add logic_symbol.result)
    program.registry.logic_by_name;
  List.iter
    (fun (axiom : Typed_core.axiom) ->
      List.iter (fun (_, sort) -> add sort) axiom.variables)
    program.registry.axioms;
  List.iter
    (fun (lemma : Typed_core.axiom) ->
      List.iter (fun (_, sort) -> add sort) lemma.variables)
    program.registry.checked_lemmas;
  Hashtbl.fold (fun _ sort result -> sort :: result) values []

let typed_datatype_prelude program function_def =
  let buffer = Buffer.create 4096 in
  let line format =
    Printf.kbprintf (fun _ -> Buffer.add_char buffer '\n') buffer format
  in
  let datatype_sort_names =
    List.map
      (fun (datatype : Typed_core.datatype) ->
        typed_smt_sort datatype.Typed_core.owner)
      program.Typed_core.registry.datatypes
  in
  typed_collect_sorts program function_def
  |> List.iter (fun sort ->
      if
        sort <> "Int" && sort <> "Bool"
        && not (List.mem sort datatype_sort_names)
      then line "(declare-sort %s 0)" sort);
  List.iter
    (fun (datatype : Typed_core.datatype) ->
      line "(declare-sort %s 0)" (typed_smt_sort datatype.Typed_core.owner))
    program.registry.datatypes;
  typed_collect_sort_values program function_def
  |> List.iter (function
    | Typed_core.S_tuple elements as tuple_sort ->
        let tuple_name = typed_smt_sort tuple_sort in
        let constructor = typed_tuple_constructor tuple_sort in
        line "(declare-fun %s (%s) %s)" constructor
          (String.concat " " (List.map typed_smt_sort elements))
          tuple_name;
        List.iteri
          (fun index sort ->
            line "(declare-fun %s (%s) %s)"
              (typed_tuple_selector tuple_sort index)
              tuple_name (typed_smt_sort sort))
          elements;
        let arguments =
          List.mapi
            (fun index sort -> ("t" ^ string_of_int index, sort))
            elements
        in
        let binders =
          "("
          ^ String.concat " "
              (List.map
                 (fun (name, sort) ->
                   Printf.sprintf "(%s %s)" name (typed_smt_sort sort))
                 arguments)
          ^ ")"
        in
        let constructed = app constructor (List.map fst arguments) in
        List.iteri
          (fun index _ ->
            line "(assert (forall %s (= (%s %s) %s)))" binders
              (typed_tuple_selector tuple_sort index)
              constructed
              (fst (List.nth arguments index)))
          elements;
        let fields =
          List.mapi
            (fun index _ -> app (typed_tuple_selector tuple_sort index) [ "v" ])
            elements
        in
        line "(assert (forall ((v %s)) (= v %s)))" tuple_name
          (app constructor fields)
    | _ -> ());
  let declared_logic = Hashtbl.create 16 in
  Hashtbl.iter
    (fun _ (logic_symbol : Typed_core.logic_symbol) ->
      let name = typed_logic_name logic_symbol in
      if not (Hashtbl.mem declared_logic name) then (
        Hashtbl.add declared_logic name ();
        line "(declare-fun %s (%s) %s)" name
          (String.concat " " (List.map typed_smt_sort logic_symbol.arguments))
          (typed_smt_sort logic_symbol.result)))
    program.registry.logic_by_name;
  let emit_statement provenance (axiom : Typed_core.axiom) =
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
    let body = typed_formula ~scope:axiom.scope program.registry env formula in
    let binders =
      "("
      ^ String.concat " "
          (List.map
             (fun (name, sort) ->
               Printf.sprintf "(%s %s)" (smt_identifier name)
                 (typed_smt_sort sort))
             axiom.variables)
      ^ ")"
    in
    let assertion =
      if axiom.variables = [] then body else app "forall" [ binders; body ]
    in
    line "; %s: %s" provenance axiom.axiom_name;
    line "(assert %s)" assertion
  in
  List.rev program.registry.axioms |> List.iter (emit_statement "trusted axiom");
  List.rev program.registry.checked_lemmas
  |> List.iter (emit_statement "checked lemma");
  List.iter
    (fun (datatype : Typed_core.datatype) ->
      let result = typed_smt_sort datatype.Typed_core.owner in
      List.iter
        (fun (constructor : Typed_core.constructor) ->
          line "(declare-fun %s (%s) %s)"
            (typed_constructor_name constructor)
            (String.concat " "
               (List.map typed_smt_sort constructor.Typed_core.arguments))
            result;
          line "(declare-fun %s (%s) Bool)"
            (typed_recognizer constructor)
            result;
          List.iteri
            (fun index sort ->
              line "(declare-fun %s (%s) %s)"
                (typed_selector constructor index)
                result (typed_smt_sort sort))
            constructor.arguments)
        datatype.constructors)
    program.registry.datatypes;
  List.iter
    (fun (datatype : Typed_core.datatype) ->
      let result = typed_smt_sort datatype.Typed_core.owner in
      List.iter
        (fun (constructor : Typed_core.constructor) ->
          let arguments =
            List.mapi
              (fun index sort -> ("a" ^ string_of_int index, sort))
              constructor.Typed_core.arguments
          in
          let terms = List.map fst arguments in
          let value =
            if terms = [] then typed_constructor_name constructor
            else app (typed_constructor_name constructor) terms
          in
          let quantify formula =
            if arguments = [] then formula
            else
              app "forall"
                [
                  "("
                  ^ String.concat " "
                      (List.map
                         (fun (name, sort) ->
                           Printf.sprintf "(%s %s)" name (typed_smt_sort sort))
                         arguments)
                  ^ ")";
                  formula;
                ]
          in
          line "(assert %s)"
            (quantify (app (typed_recognizer constructor) [ value ]));
          List.iteri
            (fun index _ ->
              line "(assert %s)"
                (quantify
                   (app "="
                      [
                        app (typed_selector constructor index) [ value ];
                        List.nth terms index;
                      ])))
            constructor.arguments;
          List.iter
            (fun (other : Typed_core.constructor) ->
              if other.Typed_core.symbol.key <> constructor.symbol.key then
                line "(assert %s)"
                  (quantify
                     (app "not" [ app (typed_recognizer other) [ value ] ])))
            datatype.constructors)
        datatype.constructors;
      line "(assert (forall ((v %s)) %s))" result
        (or_
           (List.map
              (fun (constructor : Typed_core.constructor) ->
                app (typed_recognizer constructor) [ "v" ])
              datatype.constructors));
      List.iter
        (fun (constructor : Typed_core.constructor) ->
          let fields =
            List.mapi
              (fun index _ -> app (typed_selector constructor index) [ "v" ])
              constructor.Typed_core.arguments
          in
          let rebuilt =
            if fields = [] then typed_constructor_name constructor
            else app (typed_constructor_name constructor) fields
          in
          line "(assert (forall ((v %s)) (=> (%s v) (= v %s))))" result
            (typed_recognizer constructor)
            rebuilt)
        datatype.constructors)
    program.registry.datatypes;
  Buffer.contents buffer

let typed_obligation (program : Typed_core.program) analysis
    (function_def : Typed_core.function_def) (contract : Typed_core.contract) =
  let env =
    List.map
      (fun (symbol, _) ->
        ( symbol.Typed_core.key,
          { term = smt_identifier symbol.key; refinement = None } ))
      function_def.Typed_core.arguments
  in
  let formula_env =
    List.map2
      (fun (symbol, sort) (_, value) ->
        (symbol.Typed_core.display, (value.term, sort)))
      function_def.arguments env
  in
  let pre_expression =
    parse_formula ~filename:contract.loc.file
      ~loc:(location_of_span contract.loc)
      contract.pre
  in
  let post_expression =
    parse_formula ~filename:contract.loc.file
      ~loc:(location_of_span contract.loc)
      contract.post
  in
  let witness_expressions =
    match contract.witnesses with
    | [] -> []
    | witnesses ->
        if contract.mode <> Under then assert false;
        let names = List.map fst witnesses in
        let expected =
          List.map
            (fun ((symbol : Typed_core.symbol), _) -> symbol.display)
            function_def.arguments
        in
        if
          List.sort String.compare names <> List.sort String.compare expected
          || List.length names
             <> List.length (List.sort_uniq String.compare names)
        then
          typed_error_at contract.loc
            "coverage witnesses must define every parameter exactly once";
        List.map
          (fun ((symbol : Typed_core.symbol), sort) ->
            let text = List.assoc symbol.display witnesses in
            let expression =
              parse_formula ~filename:contract.loc.file
                ~loc:(location_of_span contract.loc)
                text
            in
            (symbol, sort, expression))
          function_def.arguments
  in
  let program =
    typed_specialize_program program function_def pre_expression post_expression
  in
  let program = typed_monomorphize_datatypes program function_def in
  let body, choices, generic_calls =
    typed_expr_smt program analysis contract.mode function_def env
      function_def.body
  in
  let roots =
    generic_calls.used_theory_symbols
    @ formula_theory_symbols program.registry formula_env pre_expression
    @ formula_theory_symbols program.registry
        (("result", ("result", function_def.result)) :: formula_env)
        post_expression
    @ List.concat_map
        (fun (_, sort, expression) ->
          formula_theory_symbols ~expected:sort program.registry
            [ ("result", ("missing_result", function_def.result)) ]
            expression)
        witness_expressions
    |> List.sort_uniq String.compare
  in
  let program, _enabled_symbols = slice_program_theory program ~roots in
  let pre = typed_formula program.registry formula_env pre_expression in
  let result_name =
    match contract.mode with Over -> "result" | Under -> "missing_result"
  in
  let post_env =
    let result = ("result", (result_name, function_def.result)) in
    if witness_expressions = [] then result :: formula_env else [ result ]
  in
  let post = typed_formula program.registry post_env post_expression in
  let argument_witnesses =
    List.map
      (fun (symbol, sort, expression) ->
        ( smt_identifier symbol.Typed_core.key,
          typed_formula ~expected:sort program.registry
            [ ("result", (result_name, function_def.result)) ]
            expression ))
      witness_expressions
  in
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer
    "(set-option :produce-models true)\n(set-logic ALL)\n";
  Buffer.add_string buffer (typed_datatype_prelude program function_def);
  Hashtbl.iter
    (fun name (arguments, result) ->
      Buffer.add_string buffer
        (Printf.sprintf "(declare-fun %s (%s) %s)\n" name
           (String.concat " " arguments)
           result))
    generic_calls.runtime_declarations;
  Vc_semantics.encode contract.mode
    {
      buffer;
      arguments =
        List.map
          (fun (symbol, sort) ->
            (smt_identifier symbol.Typed_core.key, typed_smt_sort sort))
          function_def.arguments;
      choices =
        List.map (fun (name, sort) -> (name, typed_smt_sort sort)) choices;
      result_sort = typed_smt_sort function_def.result;
      body = body.term;
      pre;
      post;
      assumptions = List.rev generic_calls.summary_assumptions;
      side_conditions = List.rev generic_calls.side_conditions;
      argument_witnesses;
    };
  Buffer.add_string buffer "(check-sat)\n(get-model)\n";
  {
    name = function_def.symbol.display;
    mode = contract.mode;
    location = contract.loc;
    smt = Buffer.contents buffer;
    trusted_axioms =
      List.rev_map
        (fun (axiom : Typed_core.axiom) -> axiom.axiom_name)
        program.registry.axioms;
    checked_lemmas =
      List.rev_map
        (fun (lemma : Typed_core.axiom) -> lemma.axiom_name)
        program.registry.checked_lemmas;
    proof_artifacts = List.rev program.registry.proof_artifacts;
    ghost_instantiations = List.rev generic_calls.ghost_instantiations;
  }

let typed_exception_obligation (program : Typed_core.program) analysis
    (function_def : Typed_core.function_def) (contract : Typed_core.contract) =
  if contract.mode <> Over then
    typed_error_at contract.loc
      "exceptionful coverage contracts are not yet supported";
  let env =
    List.map
      (fun (symbol, _) ->
        ( symbol.Typed_core.key,
          { term = smt_identifier symbol.key; refinement = None } ))
      function_def.arguments
  in
  let formula_env =
    List.map2
      (fun (symbol, sort) (_, value) ->
        (symbol.Typed_core.display, (value.term, sort)))
      function_def.arguments env
  in
  let parse text =
    parse_formula ~filename:contract.loc.file
      ~loc:(location_of_span contract.loc)
      text
  in
  let pre_expression = parse contract.pre in
  let post_expression = parse contract.post in
  let result_reference_sort = reference_content_sort function_def.result in
  let result_state_expression = Option.map parse contract.result_state in
  (match
     (result_reference_sort, result_state_expression, contract.result_fresh)
   with
  | Some _, None, _ ->
      typed_error_at contract.loc
        "a reference result requires result_state for escaping heap content"
  | None, Some _, _ ->
      typed_error_at contract.loc
        "result_state is valid only for a reference result"
  | None, None, true ->
      typed_error_at contract.loc
        "result_fresh is valid only for a reference result"
  | Some _, Some _, _ | None, None, false -> ());
  let outcome_payloads =
    typed_outcome_payload_sorts ~program function_def.body
  in
  let payload_sort kind name =
    let rec find = function
      | [] -> None
      | (candidate, candidate_name, sort) :: rest ->
          if candidate = kind && candidate_name = name then sort else find rest
    in
    find outcome_payloads
  in
  let raised_expressions =
    contract.raises
    |> List.map (fun (name, predicate) ->
        (name, payload_sort `Raised name, parse predicate))
  in
  let performed_expressions =
    contract.performs
    |> List.map (fun (name, predicate) ->
        (name, payload_sort `Performed name, parse predicate))
  in
  let local_cells = typed_local_cells function_def.body in
  let reference_cells =
    typed_reference_arguments function_def
    |> List.map (fun (name, key, sort) -> (name, smt_identifier key, sort))
  in
  let state_cells =
    local_cells
    @ List.map
        (fun (name, key, sort) -> (name, smt_identifier key, sort))
        reference_cells
  in
  let state_expressions =
    List.map
      (fun (name, predicate) ->
        match List.find_opt (fun (cell, _, _) -> cell = name) state_cells with
        | Some (_, key, sort) ->
            (name, smt_identifier key, sort, parse predicate)
        | None ->
            typed_error_at contract.loc
              "state postcondition names unknown local cell `%s`" name)
      contract.state
  in
  let reference_names = List.map (fun (name, _, _) -> name) reference_cells in
  let validate_modified name =
    if not (List.mem name reference_names) then
      typed_error_at contract.loc
        "modifies footprint names non-reference parameter `%s`" name
  in
  List.iter validate_modified contract.modifies;
  List.iter
    (fun (kind, outcome, name) ->
      validate_modified name;
      if
        (kind = "raise" && not (List.mem_assoc outcome contract.raises))
        || (kind = "perform" && not (List.mem_assoc outcome contract.performs))
        || (kind <> "raise" && kind <> "perform")
      then
        typed_error_at contract.loc
          "outcome_modifies names undeclared outcome `%s:%s`" kind outcome)
    contract.outcome_modifies;
  let normal_modified_names =
    contract.modifies
    @ List.filter_map
        (fun (name, _) ->
          if List.mem name reference_names then Some name else None)
        contract.state
    |> List.sort_uniq String.compare
  in
  let outcome_modified_names kind outcome =
    List.filter_map
      (fun (candidate_kind, candidate, name) ->
        if candidate_kind = kind && candidate = outcome then Some name else None)
      contract.outcome_modifies
    @ List.filter_map
        (fun (candidate_kind, candidate, name, _predicate) ->
          if
            candidate_kind = kind && candidate = outcome
            && List.mem name reference_names
          then Some name
          else None)
        contract.outcome_state
    |> List.sort_uniq String.compare
  in
  let required_state_expressions =
    List.map
      (fun (name, predicate) ->
        match
          List.find_opt (fun (cell, _, _) -> cell = name) reference_cells
        with
        | Some (_, key, sort) ->
            (name, smt_identifier key, sort, parse predicate)
        | None ->
            typed_error_at contract.loc
              "requires_state names non-reference parameter `%s`" name)
      contract.requires_state
  in
  let outcome_state_expressions =
    List.map
      (fun (kind, outcome, name, predicate) ->
        let payload_sort =
          match kind with
          | "raise" ->
              if not (List.mem_assoc outcome contract.raises) then
                typed_error_at contract.loc
                  "outcome_state names undeclared raised outcome `%s`" outcome;
              payload_sort `Raised outcome
          | "perform" ->
              if not (List.mem_assoc outcome contract.performs) then
                typed_error_at contract.loc
                  "outcome_state names undeclared performed outcome `%s`"
                  outcome;
              payload_sort `Performed outcome
          | _ ->
              typed_error_at contract.loc
                "outcome_state kind must be `raise` or `perform`"
        in
        match List.find_opt (fun (cell, _, _) -> cell = name) state_cells with
        | Some (_, key, sort) ->
            ( kind,
              outcome,
              name,
              smt_identifier key,
              sort,
              payload_sort,
              parse predicate )
        | None ->
            typed_error_at contract.loc "outcome_state names unknown cell `%s`"
              name)
      contract.outcome_state
  in
  let state_names = List.map fst contract.state in
  if
    List.length state_names
    <> List.length (List.sort_uniq String.compare state_names)
  then typed_error_at contract.loc "state clauses must name each cell once";
  let names = List.map fst contract.raises in
  if List.length names <> List.length (List.sort_uniq String.compare names) then
    typed_error_at contract.loc "raises clauses must name each exception once";
  let operation_names = List.map fst contract.performs in
  if
    List.length operation_names
    <> List.length (List.sort_uniq String.compare operation_names)
  then
    typed_error_at contract.loc "performs clauses must name each operation once";
  let outcome_state_names =
    List.map
      (fun (kind, outcome, name, _) -> (kind, outcome, name))
      contract.outcome_state
  in
  if
    List.length outcome_state_names
    <> List.length (List.sort_uniq compare outcome_state_names)
  then
    typed_error_at contract.loc
      "outcome_state clauses must name each outcome cell once";
  let program =
    typed_specialize_program program function_def pre_expression post_expression
    |> fun program -> typed_monomorphize_datatypes program function_def
  in
  let owned_result_paths result =
    if result_reference_sort <> None then []
    else
      match
        returned_reference_paths program.registry
          ~result_sort:function_def.result ~result
      with
      | Ok paths -> paths
      | Error path ->
          typed_error_at contract.loc
            "recursive reachable-reference path `%s` needs an ownership \
             invariant"
            path
  in
  let owned_paths = owned_result_paths "result" in
  let expected_owned_paths = List.map (fun path -> path.path) owned_paths in
  let actual_owned_paths = List.map fst contract.result_references in
  if result_reference_sort <> None then (
    if contract.result_references <> [] then
      typed_error_at contract.loc
        "direct reference results use result_state, not result_references";
    if contract.result_fresh_references <> [] then
      typed_error_at contract.loc
        "direct reference results use result_fresh, not result_fresh_references")
  else if
    List.sort String.compare expected_owned_paths
    <> List.sort String.compare actual_owned_paths
    || List.length actual_owned_paths
       <> List.length (List.sort_uniq String.compare actual_owned_paths)
  then
    typed_error_at contract.loc
      "result_references must cover every finite returned reference path";
  if
    List.exists
      (fun path -> not (List.mem path expected_owned_paths))
      contract.result_fresh_references
  then
    typed_error_at contract.loc
      "result_fresh_references names an unknown returned reference path";
  let owned_result_expressions =
    List.map
      (fun path ->
        ( path,
          parse (List.assoc path.path contract.result_references),
          List.mem path.path contract.result_fresh_references ))
      owned_paths
  in
  let relation, choices, generic_calls =
    typed_relational_expr program analysis Over function_def
      ~initial_state:
        (typed_initial_reference_state ~registry:program.registry function_def)
      env function_def.body
  in
  if owned_paths <> [] then
    use_returned_reference_theory generic_calls program.registry
      function_def.result;
  if generic_calls.summary_assumptions <> [] then
    typed_error_at contract.loc
      "effectful outcome summaries cannot use value-only assumptions";
  let roots =
    generic_calls.used_theory_symbols
    @ formula_theory_symbols program.registry formula_env pre_expression
    @ formula_theory_symbols program.registry
        (("result", ("result", function_def.result)) :: formula_env)
        post_expression
    @ Option.fold ~none:[]
        ~some:(fun expression ->
          let content_sort = Option.get result_reference_sort in
          formula_theory_symbols program.registry
            (("value", ("result_state_value", content_sort))
            :: ("result", ("result", function_def.result))
            :: formula_env)
            expression)
        result_state_expression
    @ List.concat_map
        (fun (path, expression, _fresh) ->
          formula_theory_symbols program.registry
            (("value", ("reachable_result_value", path.content_sort))
            :: ("result", ("result", function_def.result))
            :: formula_env)
            expression)
        owned_result_expressions
    @ List.concat_map
        (fun (_, payload_sort, expression) ->
          let env =
            match payload_sort with
            | Some sort -> ("payload", ("payload", sort)) :: formula_env
            | None -> formula_env
          in
          formula_theory_symbols program.registry env expression)
        raised_expressions
    @ List.concat_map
        (fun (_, payload_sort, expression) ->
          let env =
            match payload_sort with
            | Some sort -> ("payload", ("payload", sort)) :: formula_env
            | None -> formula_env
          in
          formula_theory_symbols program.registry env expression)
        performed_expressions
    @ List.concat_map
        (fun (_, _, sort, expression) ->
          formula_theory_symbols program.registry
            (("value", ("state_value", sort))
            :: ("old", ("old_state_value", sort))
            :: ("result", ("result", function_def.result))
            :: formula_env)
            expression)
        state_expressions
    @ List.concat_map
        (fun (_kind, _outcome, _name, _key, sort, payload_sort, expression) ->
          let env =
            ("value", ("state_value", sort))
            :: ("old", ("old_state_value", sort))
            :: formula_env
          in
          let env =
            match payload_sort with
            | Some payload_sort -> ("payload", ("payload", payload_sort)) :: env
            | None -> env
          in
          formula_theory_symbols program.registry env expression)
        outcome_state_expressions
    @ List.concat_map
        (fun (_, _, sort, expression) ->
          formula_theory_symbols program.registry
            (("value", ("initial_state_value", sort)) :: formula_env)
            expression)
        required_state_expressions
    |> List.sort_uniq String.compare
  in
  let program, _ = slice_program_theory program ~roots in
  let required_state_posts =
    List.map
      (fun (_name, key, sort, expression) ->
        let predicate =
          typed_formula program.registry
            (("value", ("initial_state_value", sort)) :: formula_env)
            expression
        in
        let initial_value = app "select" [ initial_heap_name sort; key ] in
        Printf.sprintf "(let ((initial_state_value %s)) %s)" initial_value
          predicate)
      required_state_expressions
  in
  let pre =
    and_
      (typed_formula program.registry formula_env pre_expression
      :: required_state_posts)
  in
  let post =
    typed_formula program.registry
      (("result", ("result", function_def.result)) :: formula_env)
      post_expression
  in
  let result_state_post =
    Option.map
      (fun expression ->
        let content_sort = Option.get result_reference_sort in
        ( content_sort,
          typed_formula program.registry
            (("value", ("result_state_value", content_sort))
            :: ("result", ("result", function_def.result))
            :: formula_env)
            expression ))
      result_state_expression
  in
  let owned_result_posts =
    List.map
      (fun (path, expression, fresh) ->
        ( path.path,
          path.content_sort,
          typed_formula program.registry
            (("value", ("reachable_result_value", path.content_sort))
            :: ("result", ("result", function_def.result))
            :: formula_env)
            expression,
          fresh ))
      owned_result_expressions
  in
  let raised =
    List.map
      (fun (name, payload_sort, expression) ->
        let env =
          match payload_sort with
          | Some sort -> ("payload", ("payload", sort)) :: formula_env
          | None -> formula_env
        in
        (name, payload_sort, typed_formula program.registry env expression))
      raised_expressions
  in
  let performed =
    List.map
      (fun (name, payload_sort, expression) ->
        let env =
          match payload_sort with
          | Some sort -> ("payload", ("payload", sort)) :: formula_env
          | None -> formula_env
        in
        (name, payload_sort, typed_formula program.registry env expression))
      performed_expressions
  in
  let state_posts =
    List.map
      (fun (name, key, sort, expression) ->
        ( name,
          key,
          sort,
          typed_formula program.registry
            (("value", ("state_value", sort))
            :: ("old", ("old_state_value", sort))
            :: ("result", ("result", function_def.result))
            :: formula_env)
            expression ))
      state_expressions
  in
  let outcome_state_posts =
    List.map
      (fun (kind, outcome, name, key, sort, payload_sort, expression) ->
        let env =
          ("value", ("state_value", sort))
          :: ("old", ("old_state_value", sort))
          :: formula_env
        in
        let env =
          match payload_sort with
          | Some payload_sort -> ("payload", ("payload", payload_sort)) :: env
          | None -> env
        in
        ( kind,
          outcome,
          name,
          key,
          sort,
          payload_sort,
          typed_formula program.registry env expression ))
      outcome_state_expressions
  in
  let bind_payload payload_sort payload predicate =
    match (payload_sort, payload) with
    | None, _ -> predicate
    | Some _, Some payload ->
        Printf.sprintf "(let ((payload %s)) %s)" payload predicate
    | Some _, None -> "false"
  in
  let initial_cell_value initial key sort =
    match List.assoc_opt key generic_calls.local_initial_values with
    | Some value -> value
    | None -> heap_select initial key sort
  in
  let abnormal_state kind outcome payload initial final =
    outcome_state_posts
    |> List.filter_map
         (fun
           (candidate_kind, candidate, _name, key, sort, payload_sort, predicate)
         ->
           if candidate_kind <> kind || candidate <> outcome then None
           else
             let value = heap_select final key sort in
             let old = initial_cell_value initial key sort in
             Some
               (bind_payload payload_sort payload
                  (Printf.sprintf
                     "(let ((state_value %s) (old_state_value %s)) %s)" value
                     old predicate)))
  in
  let obligation =
    Relational_outcome.safety_obligation ~pre
      ~normal:(fun ~value ~initial ~final ->
        let state_obligations =
          List.map
            (fun (_name, key, sort, predicate) ->
              let state_value = heap_select final key sort in
              let old_state = initial_cell_value initial key sort in
              Printf.sprintf
                "(let ((result %s) (state_value %s) (old_state_value %s)) %s)"
                value state_value old_state predicate)
            state_posts
        in
        let result_obligations =
          match result_state_post with
          | None -> []
          | Some (content_sort, predicate) ->
              let content = heap_select final value content_sort in
              let state =
                Printf.sprintf "(let ((result %s) (result_state_value %s)) %s)"
                  value content predicate
              in
              let freshness =
                if not contract.result_fresh then []
                else
                  let identities =
                    List.map (fun (_, identity, _) -> identity) reference_cells
                  in
                  match identities with
                  | [] -> []
                  | identities -> [ app "distinct" (value :: identities) ]
              in
              state :: freshness
        in
        let owned_result_obligations =
          let paths = owned_result_paths value in
          List.concat_map
            (fun (path_name, content_sort, predicate, fresh) ->
              let path = List.find (fun path -> path.path = path_name) paths in
              let content = heap_select final path.identity content_sort in
              let state =
                Printf.sprintf
                  "(let ((result %s) (reachable_result_value %s)) %s)" value
                  content predicate
              in
              let obligations = [ app "=>" [ path.guard; state ] ] in
              if not fresh then obligations
              else
                let identities =
                  List.map (fun (_, identity, _) -> identity) reference_cells
                in
                match identities with
                | [] -> obligations
                | identities ->
                    app "=>"
                      [
                        path.guard; app "distinct" (path.identity :: identities);
                      ]
                    :: obligations)
            owned_result_posts
        in
        let owned_result_distinctness =
          let paths = owned_result_paths value in
          owned_result_posts
          |> List.filter_map (fun (path_name, _sort, _predicate, fresh) ->
              if not fresh then None
              else
                let path =
                  List.find (fun path -> path.path = path_name) paths
                in
                Some (path.identity, path.content_sort, path.guard))
          |> guarded_identity_distinctness
        in
        let obligations =
          (post :: state_obligations)
          @ result_obligations @ owned_result_obligations
          @ owned_result_distinctness
          @ frame_obligations ~initial ~final ~references:reference_cells
              ~modified:
                (reference_modified_identities reference_cells
                   normal_modified_names)
        in
        Printf.sprintf "(let ((result %s)) %s)" value (and_ obligations))
      ~raised:(fun ~exception_ ~payload ~initial ~final ->
        let post =
          match
            List.find_opt (fun (name, _, _) -> name = exception_) raised
          with
          | Some (_, payload_sort, predicate) ->
              bind_payload payload_sort payload predicate
          | None -> "false"
        in
        and_
          ((post :: abnormal_state "raise" exception_ payload initial final)
          @ frame_obligations ~initial ~final ~references:reference_cells
              ~modified:
                (reference_modified_identities reference_cells
                   (outcome_modified_names "raise" exception_))))
      ~performed:(fun ~operation ~payload ~continuation:_ ~initial ~final ->
        let post =
          match
            List.find_opt (fun (name, _, _) -> name = operation) performed
          with
          | Some (_, payload_sort, predicate) ->
              bind_payload payload_sort payload predicate
          | None -> "false"
        in
        and_
          ((post :: abnormal_state "perform" operation payload initial final)
          @ frame_obligations ~initial ~final ~references:reference_cells
              ~modified:
                (reference_modified_identities reference_cells
                   (outcome_modified_names "perform" operation))))
      relation
  in
  let obligation =
    match generic_calls.side_conditions with
    | [] -> obligation
    | conditions ->
        and_ [ app "=>" [ pre; and_ (List.rev conditions) ]; obligation ]
  in
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer
    "(set-option :produce-models true)\n(set-logic ALL)\n";
  Buffer.add_string buffer (typed_datatype_prelude program function_def);
  List.iter
    (fun (symbol, sort) ->
      Buffer.add_string buffer
        (Printf.sprintf "(declare-const %s %s)\n"
           (smt_identifier symbol.Typed_core.key)
           (typed_smt_sort sort)))
    function_def.arguments;
  List.iter
    (fun (key, _heap) ->
      let sort =
        typed_function_reference_sorts ~registry:program.registry function_def
        |> List.find_opt (fun sort -> heap_key sort = key)
        |> Option.get
      in
      Buffer.add_string buffer
        (Printf.sprintf "(declare-const %s (Array %s %s))\n"
           (initial_heap_name sort)
           (typed_smt_sort (reference_sort sort))
           (typed_smt_sort sort)))
    (typed_initial_reference_state ~registry:program.registry function_def);
  List.iter
    (fun (name, sort) ->
      Buffer.add_string buffer
        (Printf.sprintf "(declare-const %s %s)\n" name (typed_smt_sort sort)))
    choices;
  List.iter
    (fun assumption ->
      Buffer.add_string buffer (Printf.sprintf "(assert %s)\n" assumption))
    (List.rev generic_calls.semantic_assumptions);
  Buffer.add_string buffer (Printf.sprintf "(assert (not %s))\n" obligation);
  Buffer.add_string buffer "(check-sat)\n(get-model)\n";
  {
    name = function_def.symbol.display;
    mode = contract.mode;
    location = contract.loc;
    smt = Buffer.contents buffer;
    trusted_axioms =
      List.rev_map
        (fun (axiom : Typed_core.axiom) -> axiom.axiom_name)
        program.registry.axioms;
    checked_lemmas =
      List.rev_map
        (fun (lemma : Typed_core.axiom) -> lemma.axiom_name)
        program.registry.checked_lemmas;
    proof_artifacts = List.rev program.registry.proof_artifacts;
    ghost_instantiations = List.rev generic_calls.ghost_instantiations;
  }

let typed_outcome_coverage_obligation (program : Typed_core.program) analysis
    (function_def : Typed_core.function_def) (contract : Typed_core.contract) =
  let module R = Relational_outcome in
  let env =
    List.map
      (fun (symbol, _) ->
        ( symbol.Typed_core.key,
          { term = smt_identifier symbol.key; refinement = None } ))
      function_def.arguments
  in
  let formula_env =
    List.map2
      (fun (symbol, sort) (_, value) ->
        (symbol.Typed_core.display, (value.term, sort)))
      function_def.arguments env
  in
  let parse text =
    parse_formula ~filename:contract.loc.file
      ~loc:(location_of_span contract.loc)
      text
  in
  let pre_expression = parse contract.pre in
  let post_expression = parse contract.post in
  let result_reference_sort = reference_content_sort function_def.result in
  let result_state_expression = Option.map parse contract.result_state in
  (match
     (result_reference_sort, result_state_expression, contract.result_fresh)
   with
  | Some _, None, _ ->
      typed_error_at contract.loc
        "a reference result requires result_state for escaping heap content"
  | None, Some _, _ ->
      typed_error_at contract.loc
        "result_state is valid only for a reference result"
  | None, None, true ->
      typed_error_at contract.loc
        "result_fresh is valid only for a reference result"
  | Some _, Some _, _ | None, None, false -> ());
  let program =
    typed_specialize_program program function_def pre_expression post_expression
    |> fun program -> typed_monomorphize_datatypes program function_def
  in
  let owned_result_paths result =
    if result_reference_sort <> None then []
    else
      match
        returned_reference_paths program.registry
          ~result_sort:function_def.result ~result
      with
      | Ok paths -> paths
      | Error path ->
          typed_error_at contract.loc
            "recursive reachable-reference path `%s` needs an ownership \
             invariant"
            path
  in
  let owned_paths = owned_result_paths "missing_result" in
  let expected_owned_paths = List.map (fun path -> path.path) owned_paths in
  let actual_owned_paths = List.map fst contract.result_references in
  if result_reference_sort <> None then (
    if contract.result_references <> [] then
      typed_error_at contract.loc
        "direct reference results use result_state, not result_references";
    if contract.result_fresh_references <> [] then
      typed_error_at contract.loc
        "direct reference results use result_fresh, not result_fresh_references")
  else if
    List.sort String.compare expected_owned_paths
    <> List.sort String.compare actual_owned_paths
    || List.length actual_owned_paths
       <> List.length (List.sort_uniq String.compare actual_owned_paths)
  then
    typed_error_at contract.loc
      "result_references must cover every finite returned reference path";
  if
    List.exists
      (fun path -> not (List.mem path expected_owned_paths))
      contract.result_fresh_references
  then
    typed_error_at contract.loc
      "result_fresh_references names an unknown returned reference path";
  let owned_result_expressions =
    List.map
      (fun path ->
        ( path,
          parse (List.assoc path.path contract.result_references),
          List.mem path.path contract.result_fresh_references ))
      owned_paths
  in
  let relation, choices, generic_calls =
    typed_relational_expr program analysis Under function_def
      ~initial_state:
        (typed_initial_reference_state ~registry:program.registry function_def)
      env function_def.body
  in
  if owned_paths <> [] then
    use_returned_reference_theory generic_calls program.registry
      function_def.result;
  if generic_calls.side_conditions <> [] then
    typed_error_at contract.loc
      "outcome coverage calls require constructive callee summaries";
  let formals =
    List.filter_map
      (fun ((symbol : Typed_core.symbol), sort) ->
        match reference_content_sort sort with
        | Some _ -> None
        | None -> Some (symbol.display, symbol.key, sort))
      function_def.arguments
  in
  let validate_witnesses witnesses =
    let expected = List.map (fun (name, _, _) -> name) formals in
    let actual = List.map fst witnesses in
    if witnesses = [] then []
    else (
      if
        List.sort String.compare expected <> List.sort String.compare actual
        || List.length actual
           <> List.length (List.sort_uniq String.compare actual)
      then
        typed_error_at contract.loc
          "outcome witnesses must define every parameter exactly once";
      List.map
        (fun (name, key, sort) ->
          (key, sort, parse (List.assoc name witnesses)))
        formals)
  in
  let normal_witnesses =
    if contract.witnesses = [] then None
    else Some (validate_witnesses contract.witnesses)
  in
  let normal_witness_relation = Option.map parse contract.witness_relation in
  let reference_cells = typed_reference_arguments function_def in
  let ghost_names = List.map fst contract.ghosts in
  let reserved_ghost_names =
    [ "result"; "payload"; "value"; "old" ]
    @ List.map (fun (name, _, _) -> name) formals
    @ List.map (fun (name, _, _) -> name) reference_cells
    @ List.map (fun (name, _, _) -> "old_" ^ name) reference_cells
    @ List.map fst contract.state
  in
  if
    List.length ghost_names
    <> List.length (List.sort_uniq String.compare ghost_names)
    || List.exists (fun name -> List.mem name reserved_ghost_names) ghost_names
  then
    typed_error_at contract.loc
      "ghost names must be unique and cannot shadow contract variables";
  let coverage_ghosts =
    List.mapi
      (fun index (name, sort) ->
        ( name,
          "coverage_ghost_" ^ string_of_int index ^ "_" ^ smt_identifier name,
          sort ))
      contract.ghosts
  in
  let ghost_env =
    List.map (fun (name, term, sort) -> (name, (term, sort))) coverage_ghosts
  in
  let old_reference_env =
    List.map
      (fun (name, key, sort) ->
        ("old_" ^ name, (app "select" [ initial_heap_name sort; key ], sort)))
      reference_cells
  in
  let state_cells = typed_local_cells function_def.body @ reference_cells in
  let state_targets =
    List.mapi
      (fun index (name, predicate) ->
        match List.find_opt (fun (cell, _, _) -> cell = name) state_cells with
        | Some (_, key, sort) ->
            ( name,
              key,
              sort,
              "missing_state_" ^ string_of_int index,
              parse predicate )
        | None ->
            typed_error_at contract.loc "coverage state names unknown cell `%s`"
              name)
      contract.state
  in
  let reference_names = List.map (fun (name, _, _) -> name) reference_cells in
  List.iter
    (fun name ->
      if not (List.mem name reference_names) then
        typed_error_at contract.loc
          "modifies footprint names non-reference parameter `%s`" name;
      if not (List.mem_assoc name contract.state) then
        typed_error_at contract.loc
          "coverage modifies `%s` needs a state target predicate" name)
    contract.modifies;
  let normal_modified_names =
    contract.modifies
    @ List.filter_map
        (fun (name, _) ->
          if List.mem name reference_names then Some name else None)
        contract.state
    |> List.sort_uniq String.compare
  in
  let outcome_modified_names kind outcome =
    List.filter_map
      (fun (candidate_kind, candidate, name) ->
        if candidate_kind = kind && candidate = outcome then Some name else None)
      contract.outcome_modifies
    @ List.filter_map
        (fun (candidate_kind, candidate, name, _predicate) ->
          if
            candidate_kind = kind && candidate = outcome
            && List.mem name reference_names
          then Some name
          else None)
        contract.outcome_state
    |> List.sort_uniq String.compare
  in
  let state_witnesses =
    let expected = List.map (fun (name, _, _) -> name) reference_cells in
    let actual = List.map fst contract.state_witnesses in
    if expected = [] && actual <> [] then
      typed_error_at contract.loc "state_witnesses name no reference parameters";
    if expected <> [] && actual <> [] then
      if
        List.sort String.compare expected <> List.sort String.compare actual
        || List.length actual
           <> List.length (List.sort_uniq String.compare actual)
      then
        typed_error_at contract.loc
          "state_witnesses must define every reference parameter exactly once";
    if actual = [] then []
    else
      List.map
        (fun (name, key, sort) ->
          (key, sort, parse (List.assoc name contract.state_witnesses)))
        reference_cells
  in
  let payload_sorts = typed_outcome_payload_sorts ~program function_def.body in
  let payload_sort kind name =
    let rec find = function
      | [] -> None
      | (candidate, candidate_name, sort) :: rest ->
          if candidate = kind && candidate_name = name then sort else find rest
    in
    find payload_sorts
  in
  let outcome_state_names =
    List.map
      (fun (kind, outcome, name, _) -> (kind, outcome, name))
      contract.outcome_state
  in
  List.iter
    (fun (kind, outcome, _name, _) ->
      if
        (kind <> "raise" && kind <> "perform")
        || not
             (List.exists
                (fun (candidate : Typed_core.coverage_outcome) ->
                  candidate.kind = kind && candidate.name = outcome)
                contract.outcomes)
      then
        typed_error_at contract.loc
          "outcome_state names undeclared coverage outcome `%s:%s`" kind outcome)
    contract.outcome_state;
  List.iter
    (fun (kind, outcome, name) ->
      if not (List.mem name reference_names) then
        typed_error_at contract.loc
          "outcome_modifies names non-reference parameter `%s`" name;
      if
        not
          (List.exists
             (fun (candidate : Typed_core.coverage_outcome) ->
               candidate.kind = kind && candidate.name = outcome)
             contract.outcomes)
      then
        typed_error_at contract.loc
          "outcome_modifies names undeclared coverage outcome `%s:%s`" kind
          outcome;
      if
        not
          (List.exists
             (fun (state_kind, state_outcome, state_name, _) ->
               state_kind = kind && state_outcome = outcome && state_name = name)
             contract.outcome_state)
      then
        typed_error_at contract.loc
          "coverage outcome modifies `%s` needs a state target predicate" name)
    contract.outcome_modifies;
  if
    List.length outcome_state_names
    <> List.length (List.sort_uniq compare outcome_state_names)
  then
    typed_error_at contract.loc
      "outcome_state clauses must name each outcome cell once";
  let outcomes =
    List.mapi
      (fun outcome_index (outcome : Typed_core.coverage_outcome) ->
        let kind =
          match outcome.kind with
          | "raise" -> `Raised
          | "perform" -> `Performed
          | kind ->
              typed_error_at contract.loc "unknown coverage outcome kind `%s`"
                kind
        in
        let sort = payload_sort kind outcome.name in
        let outcome_state =
          contract.outcome_state
          |> List.filter (fun (candidate_kind, candidate, _, _) ->
              candidate_kind = outcome.kind && candidate = outcome.name)
          |> List.mapi (fun state_index (_, _, name, predicate) ->
              match
                List.find_opt (fun (cell, _, _) -> cell = name) state_cells
              with
              | Some (_, key, sort) ->
                  ( name,
                    key,
                    sort,
                    Printf.sprintf "missing_outcome_state_%d_%d" outcome_index
                      state_index,
                    parse predicate )
              | None ->
                  typed_error_at contract.loc
                    "outcome_state names unknown cell `%s`" name)
        in
        ( kind,
          outcome.name,
          sort,
          parse outcome.post,
          validate_witnesses outcome.witnesses,
          Option.map parse outcome.witness_relation,
          outcome_state ))
      contract.outcomes
  in
  let state_target_env =
    List.map
      (fun (name, _, sort, target, _) -> (name, (target, sort)))
      state_targets
  in
  let result_state_target =
    Option.map
      (fun expression ->
        (Option.get result_reference_sort, "missing_result_state", expression))
      result_state_expression
  in
  let owned_result_targets =
    List.mapi
      (fun index (path, expression, fresh) ->
        ( path,
          "missing_result_reference_" ^ string_of_int index,
          expression,
          fresh ))
      owned_result_expressions
  in
  let result_target_env =
    ("result", ("missing_result", function_def.result))
    :: Option.fold ~none:[]
         ~some:(fun (sort, target, _) -> [ ("result_value", (target, sort)) ])
         result_state_target
    @ List.map
        (fun (path, target, _expression, _fresh) ->
          (returned_reference_value_name path.path, (target, path.content_sort)))
        owned_result_targets
    @ state_target_env
  in
  let roots =
    generic_calls.used_theory_symbols
    @ formula_theory_symbols program.registry formula_env pre_expression
    @ formula_theory_symbols program.registry
        (match (normal_witness_relation, normal_witnesses) with
        | Some _, _ | None, Some _ -> result_target_env
        | None, None -> result_target_env @ formula_env)
        post_expression
    @ Option.fold ~none:[]
        ~some:(fun (sort, target, expression) ->
          formula_theory_symbols program.registry
            (("value", (target, sort)) :: result_target_env)
            expression)
        result_state_target
    @ List.concat_map
        (fun (path, target, expression, _fresh) ->
          formula_theory_symbols program.registry
            (("value", (target, path.content_sort)) :: result_target_env)
            expression)
        owned_result_targets
    @ Option.fold ~none:[]
        ~some:(fun witnesses ->
          List.concat_map
            (fun (_, sort, expression) ->
              formula_theory_symbols ~expected:sort program.registry
                (ghost_env @ result_target_env)
                expression)
            witnesses)
        normal_witnesses
    @ Option.fold ~none:[]
        ~some:(fun relation ->
          formula_theory_symbols program.registry
            (ghost_env @ result_target_env @ formula_env @ old_reference_env)
            relation)
        normal_witness_relation
    @ List.concat_map
        (fun (_, _, sort, post, witnesses, relation, outcome_state) ->
          let payload_env =
            match sort with
            | Some sort -> [ ("payload", ("missing_payload", sort)) ]
            | None -> []
          in
          let target_env =
            List.map
              (fun (name, _, sort, target, _) -> (name, (target, sort)))
              outcome_state
            @ payload_env
          in
          let witness_env = ghost_env @ target_env in
          formula_theory_symbols program.registry target_env post
          @ List.concat_map
              (fun (_, formal_sort, expression) ->
                formula_theory_symbols ~expected:formal_sort program.registry
                  witness_env expression)
              witnesses
          @ List.concat_map
              (fun (_name, _key, state_sort, target, predicate) ->
                formula_theory_symbols program.registry
                  (("value", (target, state_sort)) :: target_env)
                  predicate)
              outcome_state
          @ Option.fold ~none:[]
              ~some:(fun relation ->
                formula_theory_symbols program.registry
                  (witness_env @ formula_env @ old_reference_env)
                  relation)
              relation
          @ List.concat_map
              (fun (_, witness_sort, expression) ->
                formula_theory_symbols ~expected:witness_sort program.registry
                  witness_env expression)
              state_witnesses)
        outcomes
    @ List.concat_map
        (fun (_name, _key, sort, target, predicate) ->
          formula_theory_symbols program.registry
            (("value", (target, sort)) :: result_target_env)
            predicate)
        state_targets
    @ List.concat_map
        (fun (_, sort, expression) ->
          formula_theory_symbols ~expected:sort program.registry
            (ghost_env @ result_target_env)
            expression)
        state_witnesses
    @ List.concat_map
        (fun (name, predicate) ->
          match
            List.find_opt (fun (cell, _, _) -> cell = name) reference_cells
          with
          | Some (_, _, sort) ->
              formula_theory_symbols program.registry
                [ ("value", ("initial_state_value", sort)) ]
                (parse predicate)
          | None ->
              typed_error_at contract.loc
                "requires_state names non-reference parameter `%s`" name)
        contract.requires_state
    |> List.sort_uniq String.compare
  in
  let program, _ = slice_program_theory program ~roots in
  let required_state_posts =
    List.map
      (fun (name, predicate) ->
        let _, key, sort =
          List.find (fun (cell, _, _) -> cell = name) reference_cells
        in
        let predicate =
          typed_formula program.registry
            [ ("value", ("initial_state_value", sort)) ]
            (parse predicate)
        in
        Printf.sprintf "(let ((initial_state_value %s)) %s)"
          (app "select" [ initial_heap_name sort; key ])
          predicate)
      contract.requires_state
  in
  let pre =
    and_
      (typed_formula program.registry formula_env pre_expression
      :: required_state_posts)
  in
  let heap_declarations =
    typed_initial_reference_state ~registry:program.registry function_def
    |> List.map (fun (key, _) ->
        let sort =
          typed_function_reference_sorts ~registry:program.registry function_def
          |> List.find_opt (fun sort -> heap_key sort = key)
          |> Option.get
        in
        ( initial_heap_name sort,
          Printf.sprintf "(Array %s %s)"
            (typed_smt_sort (reference_sort sort))
            (typed_smt_sort sort) ))
  in
  let reference_declarations =
    List.map
      (fun (_name, identity, sort) ->
        (identity, typed_smt_sort (reference_sort sort)))
      reference_cells
  in
  let choices_declarations =
    List.map (fun (name, sort) -> (name, typed_smt_sort sort)) choices
  in
  let exists_choices formula =
    Refinement_domain.Smt.exists choices_declarations formula
  in
  let ghost_declarations =
    List.map
      (fun (_name, term, sort) -> (term, typed_smt_sort sort))
      coverage_ghosts
  in
  let exists_ghosts formula =
    Refinement_domain.Smt.exists ghost_declarations formula
  in
  let ordinary_input_declarations =
    List.map (fun (_, key, sort) -> (key, typed_smt_sort sort)) formals
  in
  let reference_input_declarations =
    reference_declarations @ heap_declarations
  in
  let input_declarations =
    ordinary_input_declarations @ reference_input_declarations
  in
  let exists_inputs formula =
    Refinement_domain.Smt.exists input_declarations formula
  in
  let forall_inputs_and_ghosts formula =
    Refinement_domain.Smt.forall
      (ghost_declarations @ input_declarations)
      formula
  in
  let let_arguments target_env witnesses formula =
    let bindings =
      List.map
        (fun (key, sort, expression) ->
          ( key,
            typed_formula ~expected:sort program.registry target_env expression
          ))
        witnesses
    in
    "(let ("
    ^ String.concat " "
        (List.map
           (fun (name, term) -> Printf.sprintf "(%s %s)" name term)
           bindings)
    ^ ") " ^ formula ^ ")"
  in
  let initial_state_guards target_env =
    List.map
      (fun (identity, sort, expression) ->
        app "="
          [
            app "select" [ initial_heap_name sort; identity ];
            typed_formula ~expected:sort program.registry target_env expression;
          ])
      state_witnesses
  in
  let with_relational_assumptions target_env formula =
    and_
      (((formula :: List.rev generic_calls.summary_assumptions)
       @ List.rev generic_calls.semantic_assumptions)
      @ initial_state_guards target_env)
  in
  let normal_paths =
    relation
    |> List.filter_map (fun path ->
        match path.R.outcome with
        | Return value ->
            let state_equalities =
              List.map
                (fun (_name, key, sort, target, _) ->
                  app "=" [ heap_select path.final_state key sort; target ])
                state_targets
            in
            let result_equalities =
              Option.fold ~none:[]
                ~some:(fun (sort, target, _) ->
                  [
                    app "=" [ heap_select path.final_state value sort; target ];
                  ])
                result_state_target
            in
            let owned_result_equalities =
              let actual_paths = owned_result_paths value in
              let equalities =
                List.concat_map
                  (fun (target_path, target, _expression, fresh) ->
                    let owned_path =
                      List.find
                        (fun path -> path.path = target_path.path)
                        actual_paths
                    in
                    let content =
                      heap_select path.final_state owned_path.identity
                        owned_path.content_sort
                    in
                    let equality =
                      app "=>" [ owned_path.guard; app "=" [ content; target ] ]
                    in
                    if not fresh then [ equality ]
                    else
                      let identities =
                        List.map
                          (fun (_, identity, _) -> identity)
                          reference_cells
                      in
                      match identities with
                      | [] -> [ equality ]
                      | identities ->
                          [
                            app "=>"
                              [
                                owned_path.guard;
                                app "distinct"
                                  (owned_path.identity :: identities);
                              ];
                            equality;
                          ])
                  owned_result_targets
              in
              let distinctness =
                owned_result_targets
                |> List.filter_map
                     (fun (target_path, _target, _expression, fresh) ->
                       if not fresh then None
                       else
                         let path =
                           List.find
                             (fun path -> path.path = target_path.path)
                             actual_paths
                         in
                         Some (path.identity, path.content_sort, path.guard))
                |> guarded_identity_distinctness
              in
              equalities @ distinctness
            in
            let freshness =
              if not contract.result_fresh then []
              else
                let identities =
                  List.map (fun (_, identity, _) -> identity) reference_cells
                in
                match identities with
                | [] -> []
                | identities -> [ app "distinct" (value :: identities) ]
            in
            Some
              (and_
                 (path.guard
                  :: app "=" [ value; "missing_result" ]
                  :: state_equalities
                 @ result_equalities @ owned_result_equalities @ freshness
                 @ frame_obligations ~initial:path.initial_state
                     ~final:path.final_state ~references:reference_cells
                     ~modified:
                       (reference_modified_identities reference_cells
                          normal_modified_names)))
        | Raised _ | Performed _ -> None)
    |> or_
  in
  let normal_witness_env = ghost_env @ result_target_env in
  let normal_post_env =
    match (normal_witness_relation, normal_witnesses) with
    | Some _, _ | None, Some _ -> result_target_env
    | None, None -> result_target_env @ formula_env
  in
  let obligations =
    let state_posts =
      List.map
        (fun (_name, _key, sort, target, predicate) ->
          typed_formula program.registry
            (("value", (target, sort)) :: result_target_env)
            predicate)
        state_targets
    in
    let result_posts =
      Option.fold ~none:[]
        ~some:(fun (sort, target, expression) ->
          [
            typed_formula program.registry
              (("value", (target, sort)) :: result_target_env)
              expression;
          ])
        result_state_target
    in
    let owned_result_posts =
      List.map
        (fun (path, target, expression, _fresh) ->
          let predicate =
            typed_formula program.registry
              (("value", (target, path.content_sort)) :: result_target_env)
              expression
          in
          app "=>" [ path.guard; predicate ])
        owned_result_targets
    in
    let target =
      and_
        (typed_formula program.registry normal_post_env post_expression
         :: state_posts
        @ result_posts @ owned_result_posts)
    in
    match normal_witness_relation with
    | Some relation ->
        let relation =
          typed_formula program.registry
            (normal_witness_env @ formula_env @ old_reference_env)
            relation
        in
        let witness_assumptions =
          and_ (relation :: initial_state_guards normal_witness_env)
        in
        let totality =
          app "=>" [ target; exists_ghosts (exists_inputs witness_assumptions) ]
        in
        let execution =
          and_
            ((pre :: normal_paths :: List.rev generic_calls.summary_assumptions)
            @ List.rev generic_calls.semantic_assumptions)
          |> exists_choices
        in
        let soundness =
          app "=>" [ and_ [ target; witness_assumptions ]; execution ]
          |> forall_inputs_and_ghosts
        in
        [ totality; soundness ]
    | None ->
        let reachable =
          and_ [ pre; normal_paths ]
          |> with_relational_assumptions normal_witness_env
          |> exists_choices
        in
        let reachable =
          match normal_witnesses with
          | Some witnesses ->
              Refinement_domain.Smt.exists reference_input_declarations
                (let_arguments normal_witness_env witnesses reachable)
          | None -> exists_inputs reachable
        in
        [ app "=>" [ target; exists_ghosts reachable ] ]
  in
  let payload_declarations = ref [] in
  let outcome_obligations =
    List.mapi
      (fun index
           (kind, name, sort, post, witnesses, witness_relation, outcome_state)
         ->
        let target = "missing_payload_" ^ string_of_int index in
        let payload_env =
          match sort with
          | Some sort ->
              payload_declarations := (target, sort) :: !payload_declarations;
              [ ("payload", (target, sort)) ]
          | None -> []
        in
        let target_env =
          List.map
            (fun (name, _, sort, target, _) -> (name, (target, sort)))
            outcome_state
          @ payload_env
        in
        let witness_env = ghost_env @ target_env in
        let matching =
          relation
          |> List.filter_map (fun (path : R.path) ->
              let kind_name =
                match kind with `Raised -> "raise" | `Performed -> "perform"
              in
              let frames =
                frame_obligations ~initial:path.initial_state
                  ~final:path.final_state ~references:reference_cells
                  ~modified:
                    (reference_modified_identities reference_cells
                       (outcome_modified_names kind_name name))
              in
              let state_equalities =
                List.map
                  (fun (_name, key, state_sort, state_target, _) ->
                    app "="
                      [
                        heap_select path.final_state key state_sort;
                        state_target;
                      ])
                  outcome_state
              in
              match (kind, path.R.outcome) with
              | `Raised, Raised raised when raised.exception_ = name -> (
                  match (sort, raised.payload) with
                  | Some _, Some payload ->
                      Some
                        (and_
                           (path.guard
                            :: app "=" [ payload; target ]
                            :: state_equalities
                           @ frames))
                  | None, None ->
                      Some (and_ ((path.guard :: state_equalities) @ frames))
                  | _ -> None)
              | `Performed, Performed performed when performed.operation = name
                -> (
                  match (sort, performed.payload) with
                  | Some _, Some payload ->
                      Some
                        (and_
                           (path.guard
                            :: app "=" [ payload; target ]
                            :: state_equalities
                           @ frames))
                  | None, None ->
                      Some (and_ ((path.guard :: state_equalities) @ frames))
                  | _ -> None)
              | _ -> None)
          |> or_
        in
        let state_posts =
          List.map
            (fun (_name, _key, state_sort, state_target, predicate) ->
              typed_formula program.registry
                (("value", (state_target, state_sort)) :: target_env)
                predicate)
            outcome_state
        in
        let target_condition =
          and_ (typed_formula program.registry target_env post :: state_posts)
        in
        match witness_relation with
        | Some relation ->
            let relation =
              typed_formula program.registry
                (witness_env @ formula_env @ old_reference_env)
                relation
            in
            let witness_assumptions =
              and_ (relation :: initial_state_guards witness_env)
            in
            let totality =
              app "=>"
                [
                  target_condition;
                  exists_ghosts (exists_inputs witness_assumptions);
                ]
            in
            let execution =
              and_
                ((pre :: matching :: List.rev generic_calls.summary_assumptions)
                @ List.rev generic_calls.semantic_assumptions)
              |> exists_choices
            in
            let soundness =
              app "=>"
                [ and_ [ target_condition; witness_assumptions ]; execution ]
              |> forall_inputs_and_ghosts
            in
            and_ [ totality; soundness ]
        | None ->
            let reachable =
              and_ [ pre; matching ]
              |> with_relational_assumptions witness_env
              |> exists_choices
            in
            let reachable =
              if witnesses = [] then exists_inputs reachable
              else
                Refinement_domain.Smt.exists reference_input_declarations
                  (let_arguments witness_env witnesses reachable)
            in
            app "=>" [ target_condition; exists_ghosts reachable ])
      outcomes
  in
  let obligation = and_ (obligations @ outcome_obligations) in
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer
    "(set-option :produce-models true)\n(set-logic ALL)\n";
  Buffer.add_string buffer (typed_datatype_prelude program function_def);
  Buffer.add_string buffer
    (Printf.sprintf "(declare-const missing_result %s)\n"
       (typed_smt_sort function_def.result));
  Option.iter
    (fun (sort, target, _) ->
      Buffer.add_string buffer
        (Printf.sprintf "(declare-const %s %s)\n" target (typed_smt_sort sort)))
    result_state_target;
  List.iter
    (fun (path, target, _expression, _fresh) ->
      Buffer.add_string buffer
        (Printf.sprintf "(declare-const %s %s)\n" target
           (typed_smt_sort path.content_sort)))
    owned_result_targets;
  let identity_capacity_sorts =
    List.map (fun (_name, _identity, sort) -> sort) reference_cells
    @ List.filter_map (fun (_name, sort) -> reference_content_sort sort) choices
  in
  identity_capacity_sorts
  |> List.sort_uniq (fun left right ->
      String.compare (typed_smt_sort left) (typed_smt_sort right))
  |> List.iter (fun sort ->
      let count =
        List.fold_left
          (fun count candidate ->
            if typed_smt_sort candidate = typed_smt_sort sort then count + 1
            else count)
          0 identity_capacity_sorts
      in
      let witnesses =
        List.init count (fun index ->
            Printf.sprintf "heap_identity_witness_%s_%d"
              (smt_identifier (typed_smt_sort sort))
              index)
      in
      List.iter
        (fun witness ->
          Buffer.add_string buffer
            (Printf.sprintf "(declare-const %s %s)\n" witness
               (typed_smt_sort (reference_sort sort))))
        witnesses;
      if List.length witnesses > 1 then
        Buffer.add_string buffer
          (Printf.sprintf "(assert %s)\n" (app "distinct" witnesses)));
  List.iter
    (fun (_name, _key, sort, target, _) ->
      Buffer.add_string buffer
        (Printf.sprintf "(declare-const %s %s)\n" target (typed_smt_sort sort)))
    state_targets;
  List.iter
    (fun (_, _, _, _, _, _, outcome_state) ->
      List.iter
        (fun (_name, _key, sort, target, _) ->
          Buffer.add_string buffer
            (Printf.sprintf "(declare-const %s %s)\n" target
               (typed_smt_sort sort)))
        outcome_state)
    outcomes;
  List.iter
    (fun (name, sort) ->
      Buffer.add_string buffer
        (Printf.sprintf "(declare-const %s %s)\n" name (typed_smt_sort sort)))
    (List.rev !payload_declarations);
  Buffer.add_string buffer (Printf.sprintf "(assert (not %s))\n" obligation);
  Buffer.add_string buffer "(check-sat)\n(get-model)\n";
  {
    name = function_def.symbol.display;
    mode = contract.mode;
    location = contract.loc;
    smt = Buffer.contents buffer;
    trusted_axioms =
      List.rev_map
        (fun (axiom : Typed_core.axiom) -> axiom.axiom_name)
        program.registry.axioms;
    checked_lemmas =
      List.rev_map
        (fun (lemma : Typed_core.axiom) -> lemma.axiom_name)
        program.registry.checked_lemmas;
    proof_artifacts = List.rev program.registry.proof_artifacts;
    ghost_instantiations = List.rev generic_calls.ghost_instantiations;
  }

let lemma_obligations registry lemmas =
  let registry =
    {
      registry with
      Typed_core.lemmas = [];
      checked_lemmas = [];
      proof_artifacts = [];
    }
  in
  let obligation (lemma : Typed_core.axiom) =
    let arguments =
      List.map
        (fun (name, sort) ->
          ( Typed_core.
              { key = "lemma." ^ lemma.axiom_name ^ "." ^ name; display = name },
            sort ))
        lemma.variables
    in
    let dummy =
      Typed_core.
        {
          symbol =
            { key = "lemma." ^ lemma.axiom_name; display = lemma.axiom_name };
          arguments;
          result = S_unit;
          body =
            {
              desc = Bool true;
              sort = S_bool;
              refinement = None;
              loc = lemma.loc;
            };
          contracts = [];
          measure = None;
        }
    in
    let formula =
      parse_formula ~filename:lemma.loc.file
        ~loc:(location_of_span lemma.loc)
        lemma.body
    in
    let env =
      List.map
        (fun (name, sort) -> (name, (smt_identifier name, sort)))
        lemma.variables
    in
    let roots =
      formula_theory_symbols ~scope:lemma.scope registry env formula
    in
    let program = Typed_core.{ registry; functions = [] } in
    let program, _enabled_symbols = slice_program_theory program ~roots in
    let sliced_registry = program.Typed_core.registry in
    let body = typed_formula ~scope:lemma.scope sliced_registry env formula in
    let binders =
      String.concat " "
        (List.map
           (fun (name, sort) ->
             Printf.sprintf "(%s %s)" (smt_identifier name)
               (typed_smt_sort sort))
           lemma.variables)
    in
    let theorem =
      if lemma.variables = [] then body
      else app "forall" [ "(" ^ binders ^ ")"; body ]
    in
    let buffer = Buffer.create 4096 in
    Buffer.add_string buffer
      "(set-option :produce-models true)\n(set-logic ALL)\n";
    Buffer.add_string buffer (typed_datatype_prelude program dummy);
    Buffer.add_string buffer (Printf.sprintf "(assert (not %s))\n" theorem);
    Buffer.add_string buffer "(check-sat)\n(get-model)\n";
    {
      name = lemma.axiom_name;
      mode = Over;
      location = lemma.loc;
      smt = Buffer.contents buffer;
      trusted_axioms =
        List.rev_map
          (fun (axiom : Typed_core.axiom) -> axiom.axiom_name)
          sliced_registry.axioms;
      checked_lemmas =
        List.rev_map
          (fun (lemma : Typed_core.axiom) -> lemma.axiom_name)
          sliced_registry.checked_lemmas;
      proof_artifacts = List.rev sliced_registry.proof_artifacts;
      ghost_instantiations = [];
    }
  in
  List.map
    (fun lemma ->
      let result = obligation lemma in
      registry.checked_lemmas <- lemma :: registry.checked_lemmas;
      result)
    lemmas

let obligations_of_cmt_with_theories ~theories filename =
  let program = Ocaml_5_3_frontend.program_of_cmt ~theories filename in
  let analysis = Function_analysis.analyze program in
  List.concat_map
    (fun function_def ->
      List.map
        (fun contract ->
          if
            typed_requires_relational program function_def.Typed_core.body
            || contract.Typed_core.mode = Under
               && (contract.witness_relation <> None || contract.ghosts <> [])
            || sort_reaches_reference program.registry function_def.result
            || contract.result_state <> None
            || contract.result_fresh
            || contract.result_references <> []
            || contract.result_fresh_references <> []
          then
            if contract.Typed_core.mode = Under then
              typed_outcome_coverage_obligation program analysis function_def
                contract
            else
              typed_exception_obligation program analysis function_def contract
          else typed_obligation program analysis function_def contract)
        function_def.Typed_core.contracts)
    program.functions

let obligations_of_cmt filename =
  obligations_of_cmt_with_theories ~theories:[] filename
