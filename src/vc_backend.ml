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

let typed_constructor_name (constructor : Typed_core.constructor) =
  "C_" ^ smt_identifier constructor.Typed_core.symbol.key

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
  let names = if String.contains name '.' then [ name ] else candidates scope in
  List.find_map
    (fun candidate ->
      Hashtbl.find_opt registry.Typed_core.logic_by_name candidate)
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
                program.registry.datatypes
            with
            | Some datatype -> datatype.owner
            | None ->
                typed_error ~loc:expression.pexp_loc
                  "constructor `%s` has no registered owner" name)
        | None ->
            typed_error ~loc:expression.pexp_loc "unknown constructor `%s`" name
        )
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
    | Var _ | Int _ | Bool _ -> ()
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
    let axioms =
      List.map
        (fun (axiom : Typed_core.axiom) ->
          {
            axiom with
            variables =
              List.map
                (fun (name, sort) -> (name, substitute sort))
                axiom.variables;
          })
        program.registry.axioms
    in
    let registry = { program.registry with logic_by_name; axioms } in
    { program with registry }

let typed_formula ?(scope = []) registry env expression =
  let rec translate env expression =
    let recurse = translate env in
    match expression.Parsetree.pexp_desc with
    | Pexp_ident { txt; _ } -> (
        let name = longident_name txt in
        match List.assoc_opt name env with
        | Some term -> term
        | None -> (
            match typed_lookup_logic registry scope name with
            | Some logic_symbol when logic_symbol.arguments = [] ->
                typed_logic_name logic_symbol
            | _ ->
                typed_error ~loc:expression.pexp_loc
                  "unknown logical variable `%s`" name))
    | Pexp_constant { pconst_desc = Pconst_integer (value, _); _ } -> value
    | Pexp_construct ({ txt = Lident "true"; _ }, None) -> "true"
    | Pexp_construct ({ txt = Lident "false"; _ }, None) -> "false"
    | Pexp_construct ({ txt; _ }, argument) ->
        let name = longident_last txt in
        let constructor =
          match
            Hashtbl.find_opt registry.Typed_core.constructors_by_name name
          with
          | Some constructor -> constructor
          | None ->
              typed_error ~loc:expression.pexp_loc "unknown constructor `%s`"
                name
        in
        let arguments =
          match argument with
          | None -> []
          | Some { pexp_desc = Pexp_tuple expressions; _ } ->
              List.map recurse expressions
          | Some expression -> [ recurse expression ]
        in
        if arguments = [] then typed_constructor_name constructor
        else app (typed_constructor_name constructor) arguments
    | Pexp_apply
        ( { pexp_desc = Pexp_ident { txt = Lident "not"; _ }; _ },
          [ (Nolabel, argument) ] ) ->
        app "not" [ recurse argument ]
    | Pexp_apply ({ pexp_desc = Pexp_ident { txt; _ }; _ }, arguments) -> (
        let name = longident_name txt in
        let arguments =
          List.map
            (function
              | Nolabel, argument -> recurse argument
              | _ ->
                  typed_error ~loc:expression.pexp_loc
                    "logical applications cannot use labels")
            arguments
        in
        match (binary_operator name, arguments) with
        | Some operator, [ left; right ] -> app operator [ left; right ]
        | _ -> (
            match typed_lookup_logic registry scope name with
            | Some logic_symbol ->
                if List.length arguments <> List.length logic_symbol.arguments
                then
                  typed_error ~loc:expression.pexp_loc
                    "logical predicate `%s` expects %d arguments" name
                    (List.length logic_symbol.arguments);
                app (typed_logic_name logic_symbol) arguments
            | None ->
                typed_error ~loc:expression.pexp_loc
                  "unknown logical predicate `%s`" name))
    | Pexp_field (record, { txt; _ }) ->
        let name = longident_last txt in
        let constructor, index =
          match Hashtbl.find_opt registry.fields_by_name name with
          | Some entry -> entry
          | None ->
              typed_error ~loc:expression.pexp_loc
                "unknown logical record field `%s`" name
        in
        app (typed_selector constructor index) [ recurse record ]
    | _ -> typed_error ~loc:expression.pexp_loc "unsupported refinement formula"
  in
  translate env expression

let typed_pattern_smt env scrutinee pattern =
  let rec translate env scrutinee = function
    | Typed_core.Pat_any -> ("true", env)
    | Pat_var symbol -> ("true", (symbol.key, scrutinee) :: env)
    | Pat_alias (inner, symbol) ->
        let guard, env = translate env scrutinee inner in
        (guard, (symbol.key, scrutinee) :: env)
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
  mutable ghost_instantiations : string list;
}

let new_generic_call_state () =
  {
    runtime_declarations = Hashtbl.create 8;
    side_conditions = [];
    ghost_instantiations = [];
  }

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

let rec typed_expr_smt_with_choices (program : Typed_core.program) call_stack
    choices generic_calls env expression =
  let registry = program.registry in
  let _sort = expression.Typed_core.sort in
  let recurse =
    typed_expr_smt_with_choices program call_stack choices generic_calls env
  in
  match expression.Typed_core.desc with
  | Var symbol -> (
      match List.assoc_opt symbol.key env with
      | Some term -> term
      | None ->
          typed_error_at expression.loc "unsupported global value `%s`"
            symbol.display)
  | Int value -> string_of_int value
  | Bool value -> string_of_bool value
  | Construct (constructor, arguments) | Record (constructor, arguments) ->
      let arguments = List.map recurse arguments in
      if arguments = [] then typed_constructor_name constructor
      else app (typed_constructor_name constructor) arguments
  | Choose [ left; right ] ->
      let name = "choice_" ^ string_of_int (List.length !choices) in
      choices := (name, Typed_core.S_bool) :: !choices;
      app "ite" [ name; recurse left; recurse right ]
  | Choose _ ->
      typed_error_at expression.loc
        "the MVP choose primitive currently requires exactly two alternatives"
  | Apply (symbol, arguments)
    when Hashtbl.mem program.registry.generic_schemes_by_name symbol.key ->
      let scheme =
        Hashtbl.find program.registry.generic_schemes_by_name symbol.key
      in
      let actual_types =
        List.map
          (fun (argument : Typed_core.expr) ->
            match argument.refinement with
            | Some refinement -> refinement
            | None ->
                typed_error_at argument.loc
                  "argument to generic `%s` needs [@refined.type]"
                  symbol.display)
          arguments
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
             (generic_constraint_smt ~loc:expression.loc)
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
      app runtime_name (List.map recurse arguments)
  | Apply (symbol, [ left; right ]) -> (
      match binary_operator symbol.display with
      | Some operator -> app operator [ recurse left; recurse right ]
      | None -> (
          match typed_lookup_logic registry [] symbol.key with
          | Some logic_symbol ->
              if List.length logic_symbol.arguments <> 2 then
                typed_error_at expression.loc
                  "logical predicate `%s` has an unsupported application arity"
                  symbol.display;
              app
                (typed_logic_name logic_symbol)
                [ recurse left; recurse right ]
          | None ->
              typed_inline_call program call_stack choices generic_calls env
                expression symbol [ left; right ]))
  | Apply (symbol, [ argument ]) when symbol.display = "not" ->
      app "not" [ recurse argument ]
  | Apply (symbol, _) -> (
      let arguments =
        match expression.desc with
        | Apply (_, arguments) -> arguments
        | _ -> assert false
      in
      match typed_lookup_logic registry [] symbol.key with
      | Some logic_symbol ->
          if List.length arguments <> List.length logic_symbol.arguments then
            typed_error_at expression.loc
              "logical predicate `%s` has an unsupported application arity"
              symbol.display;
          app (typed_logic_name logic_symbol) (List.map recurse arguments)
      | None ->
          typed_inline_call program call_stack choices generic_calls env
            expression symbol arguments)
  | If (condition, if_true, if_false) ->
      app "ite" [ recurse condition; recurse if_true; recurse if_false ]
  | Let (symbol, value, body) ->
      let value = recurse value in
      typed_expr_smt_with_choices program call_stack choices generic_calls
        ((symbol.key, value) :: env)
        body
  | Match (scrutinee, cases) ->
      let scrutinee = recurse scrutinee in
      let translated =
        List.map
          (fun (pattern, body) ->
            let guard, case_env = typed_pattern_smt env scrutinee pattern in
            ( guard,
              typed_expr_smt_with_choices program call_stack choices
                generic_calls case_env body ))
          cases
      in
      let rec tree = function
        | [] -> typed_error_at expression.loc "empty match"
        | [ (_, body) ] -> body
        | (guard, body) :: rest -> app "ite" [ guard; body; tree rest ]
      in
      tree translated
  | Field (constructor, index, record) ->
      app (typed_selector constructor index) [ recurse record ]
  | Tuple elements ->
      app (typed_tuple_constructor expression.sort) (List.map recurse elements)

and typed_inline_call program call_stack choices generic_calls env expression
    symbol arguments =
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
      if List.mem symbol.key call_stack then
        typed_error_at expression.loc
          "recursive call to `%s` requires a measure/summary" symbol.display;
      if List.length arguments <> List.length function_def.arguments then
        typed_error_at expression.loc
          "call to `%s` has unsupported partial arity" symbol.display;
      let terms =
        List.map
          (typed_expr_smt_with_choices program call_stack choices generic_calls
             env)
          arguments
      in
      let call_env =
        List.map2
          (fun (argument, _) term -> (argument.Typed_core.key, term))
          function_def.arguments terms
      in
      typed_expr_smt_with_choices program (symbol.key :: call_stack) choices
        generic_calls call_env function_def.body

let typed_expr_smt program env expression =
  let choices = ref [] in
  let generic_calls = new_generic_call_state () in
  let term =
    typed_expr_smt_with_choices program [] choices generic_calls env expression
  in
  (term, List.rev !choices, generic_calls)

let typed_collect_sorts program function_def =
  let module Set = Set.Make (String) in
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
  let rec add sort =
    Hashtbl.replace values (typed_smt_sort sort) sort;
    match sort with
    | Typed_core.S_tuple sorts | S_app (_, sorts) -> List.iter add sorts
    | S_int | S_bool | S_unit | S_var _ -> ()
  in
  List.iter (fun (_, sort) -> add sort) function_def.Typed_core.arguments;
  add function_def.result;
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
  List.iter
    (fun (datatype : Typed_core.datatype) ->
      line "(declare-sort %s 0)" (typed_smt_sort datatype.Typed_core.owner))
    program.registry.datatypes;
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
  List.rev program.registry.axioms
  |> List.iter (fun (axiom : Typed_core.axiom) ->
      let formula =
        parse_formula ~filename:axiom.loc.file
          ~loc:(location_of_span axiom.loc)
          axiom.body
      in
      let env =
        List.map (fun (name, _) -> (name, smt_identifier name)) axiom.variables
      in
      let body =
        typed_formula ~scope:axiom.scope program.registry env formula
      in
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
      line "; trusted axiom: %s" axiom.axiom_name;
      line "(assert %s)" assertion);
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

let typed_obligation (program : Typed_core.program)
    (function_def : Typed_core.function_def) (contract : Typed_core.contract) =
  let env =
    List.map
      (fun (symbol, _) -> (symbol.Typed_core.key, smt_identifier symbol.key))
      function_def.Typed_core.arguments
  in
  let formula_env =
    List.map2
      (fun (symbol, _) (_, term) -> (symbol.Typed_core.display, term))
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
  let program =
    typed_specialize_program program function_def pre_expression post_expression
  in
  let body, choices, generic_calls =
    typed_expr_smt program env function_def.body
  in
  let pre = typed_formula program.registry formula_env pre_expression in
  let result_name =
    match contract.mode with Over -> "result" | Under -> "missing_result"
  in
  let post =
    typed_formula program.registry
      (("result", result_name) :: formula_env)
      post_expression
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
      body;
      pre;
      post;
      side_conditions = List.rev generic_calls.side_conditions;
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
    ghost_instantiations = List.rev generic_calls.ghost_instantiations;
  }

let obligations_of_cmt_with_theories ~theories filename =
  let program = Ocaml_5_3_frontend.program_of_cmt ~theories filename in
  List.concat_map
    (fun function_def ->
      List.map
        (typed_obligation program function_def)
        function_def.Typed_core.contracts)
    program.functions

let obligations_of_cmt filename =
  obligations_of_cmt_with_theories ~theories:[] filename
