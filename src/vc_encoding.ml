open Refined_ir
open Refined_types
open Refined_common
open Vc_logic
open Heap_model
open Ownership

type smt_value = {
  term : string;
  refinement : Generic_refinement.type_ option;
  closure : closure option;
}

and closure =
  | Direct_closure of {
      symbol : Typed_core.symbol;
      captured : (smt_value * Typed_core.sort) list;
      specification : Typed_core.refined_type option;
      environment : (string * (string * Typed_core.sort)) list;
    }
  | Choice_closure of {
      condition : string;
      if_true : closure;
      if_false : closure;
    }
  | Abstract_closure of {
      specification : Typed_core.refined_type;
      environment : (string * (string * Typed_core.sort)) list;
      identity : string;
      function_sort : Typed_core.sort;
    }
  | Local_closure of {
      parameters : (Typed_core.symbol * Typed_core.sort) list;
      body : Typed_core.expr;
      environment : (string * smt_value) list;
    }

let value_term ~loc value =
  match value.closure with
  | None -> value.term
  | Some _ ->
      typed_error_at loc
        "a function value escaped into the first-order logical term language"

let termination_measure_sort (function_def : Typed_core.function_def) measure =
  List.find_map
    (fun ((argument : Typed_core.symbol), sort) ->
      if argument.key = measure.Typed_core.key then Some sort else None)
    function_def.arguments
  |> Option.get

let termination_decrease ~loc (function_def : Typed_core.function_def) measures
    ~callee ~caller =
  if List.length measures <> List.length callee || callee = [] then
    typed_error_at loc "recursive call has an incompatible termination measure";
  let strict measure callee caller =
    match termination_measure_sort function_def measure with
    | Typed_core.S_int ->
        and_ [ app ">=" [ caller; "0" ]; app "<" [ callee; caller ] ]
    | _ ->
        let direct_selector_suffix = " " ^ caller ^ ")" in
        if
          callee <> caller
          && String.starts_with ~prefix:"(sel_" callee
          && String.ends_with ~suffix:direct_selector_suffix callee
        then "true"
        else "false"
  in
  let rec lexicographic equal_prefix measures callee caller =
    match (measures, callee, caller) with
    | measure :: measures, callee :: callees, caller :: callers ->
        let here = and_ (equal_prefix @ [ strict measure callee caller ]) in
        let later =
          lexicographic
            (equal_prefix @ [ app "=" [ callee; caller ] ])
            measures callees callers
        in
        if later = "false" then here else or_ [ here; later ]
    | [], [], [] -> "false"
    | _ -> assert false
  in
  let decrease = lexicographic [] measures callee caller in
  if decrease = "false" then
    typed_error_at loc
      "structural recursive measure must pass a direct constructor field";
  decrease

let contract_argument_env (function_def : Typed_core.function_def)
    (contract : Typed_core.contract) =
  let rec build formula_env env arguments domains =
    match (arguments, domains) with
    | [], [] -> List.rev env
    | ( ((symbol : Typed_core.symbol), sort) :: arguments,
        (parameter, domain) :: domains ) ->
        let term = smt_identifier symbol.key in
        let closure =
          match domain with
          | Typed_core.Refined_base _ -> None
          | Refined_arrow _ ->
              Some
                (Abstract_closure
                   {
                     specification = domain;
                     environment = formula_env;
                     identity = term;
                     function_sort = sort;
                   })
        in
        let value = { term; refinement = None; closure } in
        build
          ((parameter, (term, sort)) :: formula_env)
          ((symbol.key, value) :: env)
          arguments domains
    | _ -> invalid_arg "contract argument arity mismatch"
  in
  build [] [] function_def.arguments (Typed_core.contract_domains contract)

let typed_pattern_smt env scrutinee pattern =
  let rec translate env scrutinee = function
    | Typed_core.Pat_any -> ("true", env)
    | Pat_var symbol ->
        ( "true",
          (symbol.key, { term = scrutinee; refinement = None; closure = None })
          :: env )
    | Pat_alias (inner, symbol) ->
        let guard, env = translate env scrutinee inner in
        ( guard,
          (symbol.key, { term = scrutinee; refinement = None; closure = None })
          :: env )
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
        if constructor.result = Typed_core.S_unit && patterns = [] then
          (app "=" [ scrutinee; "unit" ], env)
        else
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
          ( and_ (app (typed_recognizer constructor) [ scrutinee ] :: guards),
            env )
  in
  translate env scrutinee pattern

type generic_call_state = {
  runtime_declarations : (string, string list * string) Hashtbl.t;
  abstract_results : (string, string * Typed_core.sort) Hashtbl.t;
  abstract_observations :
    (string, (string * string * Typed_core.sort) list) Hashtbl.t;
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
    abstract_results = Hashtbl.create 16;
    abstract_observations = Hashtbl.create 8;
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

let contract_domain_expressions (contract : Typed_core.contract) =
  let parse text =
    parse_formula ~filename:contract.loc.file
      ~loc:(location_of_span contract.loc)
      text
  in
  Typed_core.contract_domains contract
  |> List.mapi (fun index (parameter, domain) -> (index, parameter, domain))
  |> List.filter_map (fun (index, parameter, domain) ->
      match domain with
      | Typed_core.Refined_base domain ->
          Some
            ( index,
              Typed_core.rename_identifier ~from:domain.value_name
                ~into:parameter domain.predicate
              |> parse )
      | Refined_arrow _ -> None)

let contract_expressions (contract : Typed_core.contract) =
  let parse text =
    parse_formula ~filename:contract.loc.file
      ~loc:(location_of_span contract.loc)
      text
  in
  let domains = List.map snd (contract_domain_expressions contract) in
  let result =
    match Typed_core.contract_result contract with
    | Typed_core.Refined_base result -> result
    | Refined_arrow _ ->
        typed_error_at contract.loc
          "function-valued contract results are not supported by this VC"
  in
  let post =
    Typed_core.rename_identifier ~from:result.value_name ~into:"result"
      result.predicate
    |> parse
  in
  (domains, post)

let eta_expand_function_result (function_def : Typed_core.function_def)
    (contract : Typed_core.contract) =
  match Typed_core.contract_result contract with
  | Typed_core.Refined_base _ -> (function_def, contract, 0)
  | result_type ->
      let rec arguments index bindings expressions = function
        | Typed_core.Refined_base result ->
            (List.rev bindings, List.rev expressions, result)
        | Refined_arrow { parameter; domain; codomain } ->
            let sort = Typed_core.refined_sort domain in
            let symbol =
              Typed_core.
                {
                  key =
                    function_def.symbol.key ^ ".returned_argument."
                    ^ string_of_int index;
                  display = parameter;
                }
            in
            let expression =
              Typed_core.
                {
                  desc = Var symbol;
                  sort;
                  refinement = None;
                  loc = contract.loc;
                }
            in
            arguments (index + 1)
              ((symbol, sort) :: bindings)
              (expression :: expressions)
              codomain
      in
      let returned_arguments, applications, result =
        arguments 0 [] [] result_type
      in
      let body =
        Typed_core.
          {
            desc = Apply_value (function_def.body, applications);
            sort = result.base_sort;
            refinement = None;
            loc = function_def.body.loc;
          }
      in
      ( {
          function_def with
          arguments = function_def.arguments @ returned_arguments;
          result = result.base_sort;
          body;
        },
        {
          contract with
          function_arity =
            contract.function_arity + List.length returned_arguments;
        },
        List.length returned_arguments )

let instantiate_function_at_call_sorts ~loc
    (function_def : Typed_core.function_def) argument_sorts result_sort =
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
    (fun (_, formal) actual -> unify formal actual)
    function_def.arguments argument_sorts;
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
      | Apply_value (callee, expressions) ->
          Apply_value
            (map_expression callee, List.map map_expression expressions)
      | Lambda (parameters, body) ->
          Lambda
            ( List.map
                (fun (parameter, sort) -> (parameter, substitute sort))
                parameters,
              map_expression body )
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
          let rec refined_type = function
            | Typed_core.Refined_base base ->
                Refined_base { base with base_sort = substitute base.base_sort }
            | Refined_arrow { parameter; domain; codomain } ->
                Refined_arrow
                  {
                    parameter;
                    domain = refined_type domain;
                    codomain = refined_type codomain;
                  }
          in
          {
            contract with
            refined_type = refined_type contract.refined_type;
            ghosts =
              List.map
                (fun (name, sort) -> (name, substitute sort))
                contract.ghosts;
          })
        function_def.contracts;
  }

let instantiate_function_at_call ~loc function_def arguments result_sort =
  instantiate_function_at_call_sorts ~loc function_def
    (List.map (fun (argument : Typed_core.expr) -> argument.sort) arguments)
    result_sort

let rec drop_refined_arguments count type_ =
  if count = 0 then type_
  else
    match type_ with
    | Typed_core.Refined_arrow { codomain; _ } ->
        drop_refined_arguments (count - 1) codomain
    | Typed_core.Refined_base _ ->
        invalid_arg "captured closure exceeds contract arity"

let typed_refinement_predicate program generic_calls ~loc environment
    (base : Typed_core.refined_base) value =
  let formula =
    Typed_core.rename_identifier ~from:base.value_name ~into:"__value"
      base.predicate
    |> parse_formula ~filename:loc.Source_span.file ~loc:(location_of_span loc)
  in
  let environment = ("__value", (value, base.base_sort)) :: environment in
  formula_theory_symbols program.Typed_core.registry environment formula
  |> List.iter (use_theory_symbol generic_calls);
  typed_formula program.registry environment formula

(* A call may use facts established by earlier calls. Snapshot the environment
   here: including later summaries would let a call justify its own domain. *)
let add_call_side_condition state path predicate =
  state.side_conditions <-
    under_path (state.summary_assumptions @ path) predicate
    :: state.side_conditions

(* [actual <: expected] is a semantic judgment.  Base refinements generate an
   implication, while arrows are contravariant in their domain and covariant
   in their codomain.  A residual closure carries the environment for binders
   consumed by partial application, so dependent codomains keep their meaning. *)
let emit_refined_subtype program choices generic_calls path ~loc
    ~actual_environment ~expected_environment actual expected =
  let fresh sort =
    let name = "subtype_value_" ^ string_of_int (List.length !choices) in
    choices := (name, sort) :: !choices;
    name
  in
  let predicate = typed_refinement_predicate program generic_calls ~loc in
  let rec subtype path actual_environment expected_environment actual expected =
    match (actual, expected) with
    | Typed_core.Refined_base actual, Typed_core.Refined_base expected ->
        if actual.base_sort <> expected.base_sort then
          typed_error_at loc "refinement subtype sort mismatch: %s is not %s"
            (typed_smt_sort actual.base_sort)
            (typed_smt_sort expected.base_sort);
        let value = fresh actual.base_sort in
        let actual = predicate actual_environment actual value in
        let expected = predicate expected_environment expected value in
        add_call_side_condition generic_calls path
          (app "=>" [ actual; expected ])
    | Typed_core.Refined_arrow actual, Typed_core.Refined_arrow expected ->
        if
          Typed_core.refined_sort actual.domain
          <> Typed_core.refined_sort expected.domain
        then
          typed_error_at loc
            "refinement arrow domain sort mismatch: %s is not %s"
            (typed_smt_sort (Typed_core.refined_sort actual.domain))
            (typed_smt_sort (Typed_core.refined_sort expected.domain));
        subtype path expected_environment actual_environment expected.domain
          actual.domain;
        let argument_sort = Typed_core.refined_sort expected.domain in
        let argument = fresh argument_sort in
        let actual_environment =
          (actual.parameter, (argument, argument_sort)) :: actual_environment
        in
        let expected_environment =
          (expected.parameter, (argument, argument_sort))
          :: expected_environment
        in
        let codomain_path =
          match expected.domain with
          | Typed_core.Refined_base expected_domain ->
              predicate expected_environment expected_domain argument :: path
          | Refined_arrow _ -> path
        in
        subtype codomain_path actual_environment expected_environment
          actual.codomain expected.codomain
    | Typed_core.Refined_base _, Typed_core.Refined_arrow _
    | Typed_core.Refined_arrow _, Typed_core.Refined_base _ ->
        typed_error_at loc "refinement subtype shape mismatch"
  in
  subtype path actual_environment expected_environment actual expected

let rec emit_closure_subtype program choices generic_calls path ~loc
    ~expected_environment expected = function
  | Abstract_closure { specification; environment; _ } ->
      emit_refined_subtype program choices generic_calls path ~loc
        ~actual_environment:environment ~expected_environment specification
        expected
  | Choice_closure { condition; if_true; if_false } ->
      emit_closure_subtype program choices generic_calls (condition :: path)
        ~loc ~expected_environment expected if_true;
      emit_closure_subtype program choices generic_calls
        (app "not" [ condition ] :: path)
        ~loc ~expected_environment expected if_false
  | Direct_closure { specification = Some specification; environment; _ } ->
      emit_refined_subtype program choices generic_calls path ~loc
        ~actual_environment:environment ~expected_environment specification
        expected
  | Direct_closure { symbol; specification = None; _ } ->
      typed_error_at loc
        "function argument `%s` needs a safety refinement contract"
        symbol.display
  | Local_closure _ ->
      typed_error_at loc
        "internal error: local closure needs bidirectional refinement checking"

let rec typed_expr_smt_with_choices (program : Typed_core.program) analysis mode
    current_function path call_stack choices generic_calls env expression =
  let registry = program.registry in
  let _sort = expression.Typed_core.sort in
  let recurse =
    typed_expr_smt_with_choices program analysis mode current_function path
      call_stack choices generic_calls env
  in
  let make ?(refinement = expression.Typed_core.refinement) term =
    { term; refinement; closure = None }
  in
  let recurse_term (expression : Typed_core.expr) =
    value_term ~loc:expression.loc (recurse expression)
  in
  let rec apply_closure arguments path = function
    | Direct_closure { symbol; captured; _ } ->
        typed_inline_call program analysis mode current_function path call_stack
          choices generic_calls env expression ~ensure_closure_subtype ~captured
          symbol arguments
    | Choice_closure { condition; if_true; if_false } -> (
        let left = apply_closure arguments (condition :: path) if_true in
        let right =
          apply_closure arguments (app "not" [ condition ] :: path) if_false
        in
        match (left.closure, right.closure) with
        | None, None ->
            make
              (app "ite"
                 [
                   condition;
                   value_term ~loc:expression.loc left;
                   value_term ~loc:expression.loc right;
                 ])
        | Some if_true, Some if_false ->
            {
              term = "";
              refinement = expression.refinement;
              closure = Some (Choice_closure { condition; if_true; if_false });
            }
        | _ ->
            typed_error_at expression.loc
              "function branches disagree on whether application is partial")
    | Abstract_closure { specification; environment; identity; function_sort }
      ->
        let rec apply environment identity function_sort specification =
          function
          | [] ->
              {
                term = "";
                refinement = expression.refinement;
                closure =
                  Some
                    (Abstract_closure
                       { specification; environment; identity; function_sort });
              }
          | argument :: arguments -> (
              match specification with
              | Typed_core.Refined_base _ ->
                  typed_error_at expression.loc
                    "abstract function received too many arguments"
              | Refined_arrow { parameter; domain; codomain } -> (
                  let argument_value = recurse argument in
                  let argument_sort = Typed_core.refined_sort domain in
                  let argument_term, environment =
                    match domain with
                    | Refined_base base ->
                        let argument_term =
                          value_term ~loc:argument.Typed_core.loc argument_value
                        in
                        if String.trim base.predicate <> "true" then (
                          let predicate =
                            Typed_core.rename_identifier ~from:base.value_name
                              ~into:parameter base.predicate
                            |> parse_formula ~filename:expression.loc.file
                                 ~loc:(location_of_span expression.loc)
                          in
                          let predicate_env =
                            (parameter, (argument_term, argument_sort))
                            :: environment
                          in
                          formula_theory_symbols program.registry predicate_env
                            predicate
                          |> List.iter (use_theory_symbol generic_calls);
                          add_call_side_condition generic_calls path
                            (typed_formula program.registry predicate_env
                               predicate));
                        ( argument_term,
                          (parameter, (argument_term, argument_sort))
                          :: environment )
                    | Refined_arrow _ ->
                        (match argument_value.closure with
                        | None ->
                            typed_error_at argument.loc
                              "higher-order argument `%s` is not a function \
                               value"
                              parameter
                        | Some closure ->
                            ensure_closure_subtype path environment domain
                              closure);
                        let identity =
                          "closure_argument_"
                          ^ string_of_int (List.length !choices)
                        in
                        choices := (identity, argument_sort) :: !choices;
                        (identity, environment)
                  in
                  let application_key = identity ^ "(" ^ argument_term ^ ")" in
                  if arguments <> [] then
                    apply environment application_key
                      (Typed_core.refined_sort codomain)
                      codomain arguments
                  else
                    match codomain with
                    | Refined_arrow _ ->
                        {
                          term = "";
                          refinement = expression.refinement;
                          closure =
                            Some
                              (Abstract_closure
                                 {
                                   specification = codomain;
                                   environment;
                                   identity = application_key;
                                   function_sort =
                                     Typed_core.refined_sort codomain;
                                 });
                        }
                    | Refined_base result ->
                        let result_name =
                          match
                            Hashtbl.find_opt generic_calls.abstract_results
                              application_key
                          with
                          | Some (result_name, result_sort)
                            when result_sort = result.base_sort ->
                              result_name
                          | Some _ ->
                              typed_error_at expression.loc
                                "abstract closure application changed result \
                                 sort"
                          | None ->
                              let result_name =
                                "abstract_result_"
                                ^ string_of_int (List.length !choices)
                              in
                              choices :=
                                (result_name, result.base_sort) :: !choices;
                              let observations =
                                Option.value ~default:[]
                                  (Hashtbl.find_opt
                                     generic_calls.abstract_observations
                                     identity)
                              in
                              List.iter
                                (fun ( previous_argument,
                                       previous_result,
                                       previous_sort ) ->
                                  if previous_sort = result.base_sort then
                                    generic_calls.summary_assumptions <-
                                      under_path path
                                        (app "=>"
                                           [
                                             app "="
                                               [
                                                 argument_term;
                                                 previous_argument;
                                               ];
                                             app "="
                                               [ result_name; previous_result ];
                                           ])
                                      :: generic_calls.summary_assumptions)
                                observations;
                              Hashtbl.replace
                                generic_calls.abstract_observations identity
                                ((argument_term, result_name, result.base_sort)
                                :: observations);
                              Hashtbl.add generic_calls.abstract_results
                                application_key
                                (result_name, result.base_sort);
                              result_name
                        in
                        if String.trim result.predicate <> "true" then (
                          let predicate =
                            Typed_core.rename_identifier ~from:result.value_name
                              ~into:"result" result.predicate
                            |> parse_formula ~filename:expression.loc.file
                                 ~loc:(location_of_span expression.loc)
                          in
                          let predicate_env =
                            ("result", (result_name, result.base_sort))
                            :: environment
                          in
                          formula_theory_symbols program.registry predicate_env
                            predicate
                          |> List.iter (use_theory_symbol generic_calls);
                          generic_calls.summary_assumptions <-
                            under_path path
                              (typed_formula program.registry predicate_env
                                 predicate)
                            :: generic_calls.summary_assumptions);
                        {
                          term = result_name;
                          refinement = expression.refinement;
                          closure = None;
                        }))
        in
        apply environment identity function_sort specification arguments
    | Local_closure { parameters; body; environment = local_environment } ->
        let rec apply parameters local_environment arguments =
          match (parameters, arguments) with
          | [], arguments -> (
              let result =
                typed_expr_smt_with_choices program analysis mode
                  current_function path call_stack choices generic_calls
                  local_environment body
              in
              if arguments = [] then result
              else
                match result.closure with
                | Some closure -> apply_closure arguments path closure
                | None ->
                    typed_error_at expression.loc
                      "local function received too many arguments")
          | parameters, [] ->
              {
                term = "";
                refinement = expression.refinement;
                closure =
                  Some
                    (Local_closure
                       { parameters; body; environment = local_environment });
              }
          | (parameter, _) :: parameters, argument :: arguments ->
              let value = recurse argument in
              apply parameters
                ((parameter.Typed_core.key, value) :: local_environment)
                arguments
        in
        apply parameters local_environment arguments
  and ensure_closure_subtype path expected_environment expected closure =
    match closure with
    | Choice_closure { condition; if_true; if_false } ->
        ensure_closure_subtype (condition :: path) expected_environment expected
          if_true;
        ensure_closure_subtype
          (app "not" [ condition ] :: path)
          expected_environment expected if_false
    | Local_closure { parameters; body; environment = local_environment } ->
        let rec check path expected_environment local_environment parameters
            expected =
          match (parameters, expected) with
          | [], Typed_core.Refined_base expected ->
              let result =
                typed_expr_smt_with_choices program analysis mode
                  current_function path call_stack choices generic_calls
                  local_environment body
              in
              let term = value_term ~loc:body.loc result in
              let post =
                typed_refinement_predicate program generic_calls ~loc:body.loc
                  expected_environment expected term
              in
              add_call_side_condition generic_calls path post
          | [], (Typed_core.Refined_arrow _ as expected) -> (
              let result =
                typed_expr_smt_with_choices program analysis mode
                  current_function path call_stack choices generic_calls
                  local_environment body
              in
              match result.closure with
              | Some closure ->
                  ensure_closure_subtype path expected_environment expected
                    closure
              | None ->
                  typed_error_at body.loc
                    "local function result is not a function value")
          | ( (parameter, parameter_sort) :: parameters,
              Typed_core.Refined_arrow expected ) ->
              if parameter_sort <> Typed_core.refined_sort expected.domain then
                typed_error_at body.loc
                  "local function parameter sort does not match its expected \
                   refinement";
              let name =
                "local_argument_" ^ string_of_int (List.length !choices)
              in
              choices := (name, parameter_sort) :: !choices;
              let value =
                match expected.domain with
                | Typed_core.Refined_base _ ->
                    { term = name; refinement = None; closure = None }
                | Refined_arrow _ ->
                    {
                      term = "";
                      refinement = None;
                      closure =
                        Some
                          (Abstract_closure
                             {
                               specification = expected.domain;
                               environment = expected_environment;
                               identity = name;
                               function_sort = parameter_sort;
                             });
                    }
              in
              let expected_environment =
                if value.term = "" then expected_environment
                else
                  (expected.parameter, (value.term, parameter_sort))
                  :: expected_environment
              in
              let path =
                match expected.domain with
                | Typed_core.Refined_base domain ->
                    typed_refinement_predicate program generic_calls
                      ~loc:body.loc expected_environment domain name
                    :: path
                | Refined_arrow _ -> path
              in
              check path expected_environment
                ((parameter.Typed_core.key, value) :: local_environment)
                parameters expected.codomain
          | _ ->
              typed_error_at body.loc
                "local function and expected refinement have different arrow \
                 shapes"
        in
        check path expected_environment local_environment parameters expected
    | closure ->
        emit_closure_subtype program choices generic_calls path
          ~loc:expression.loc ~expected_environment expected closure
  in
  match expression.Typed_core.desc with
  | Var symbol -> (
      match List.assoc_opt symbol.key env with
      | Some value -> (
          match expression.refinement with
          | Some refinement -> { value with refinement = Some refinement }
          | None -> value)
      | None -> (
          match
            List.find_opt
              (fun (function_def : Typed_core.function_def) ->
                function_def.symbol.key = symbol.key)
              program.functions
          with
          | Some function_def ->
              let specification =
                match
                  List.filter
                    (fun (contract : Typed_core.contract) ->
                      contract.mode = Over)
                    function_def.contracts
                with
                | [ contract ] -> Some contract.refined_type
                | [] -> None
                | _ ->
                    typed_error_at expression.loc
                      "function value `%s` has ambiguous safety contracts"
                      symbol.display
              in
              {
                term = "";
                refinement = expression.refinement;
                closure =
                  Some
                    (Direct_closure
                       {
                         symbol;
                         captured = [];
                         specification;
                         environment = [];
                       });
              }
          | None ->
              typed_error_at expression.loc "unsupported global value `%s`"
                symbol.display))
  | Int value -> make (string_of_int value)
  | Bool value -> make (string_of_bool value)
  | Lambda (parameters, body) ->
      {
        term = "";
        refinement = expression.refinement;
        closure = Some (Local_closure { parameters; body; environment = env });
      }
  | Construct (constructor, arguments) | Record (constructor, arguments) ->
      use_theory_symbol generic_calls constructor.symbol.key;
      let arguments = List.map recurse_term arguments in
      make
        (if arguments = [] then typed_constructor_name constructor
         else app (typed_constructor_name constructor) arguments)
  | Choose [ left; right ]
    when left.Typed_core.sort = expression.sort
         && right.Typed_core.sort = expression.sort ->
      let name = "choice_" ^ string_of_int (List.length !choices) in
      choices := (name, Typed_core.S_bool) :: !choices;
      make (app "ite" [ name; recurse_term left; recurse_term right ])
  | Choose arguments ->
      List.iter (fun argument -> ignore (recurse_term argument)) arguments;
      let name = "choice_value_" ^ string_of_int (List.length !choices) in
      choices := (name, expression.sort) :: !choices;
      make name
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
            | None -> (
                match List.assoc_opt symbol.key env with
                | Some { closure = Some closure; _ } ->
                    apply_closure [ left; right ] path closure
                | _ ->
                    typed_inline_call program analysis mode current_function
                      path call_stack choices generic_calls env expression
                      ~ensure_closure_subtype ~captured:[] symbol
                      [ left; right ])))
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
      | None -> (
          match List.assoc_opt symbol.key env with
          | Some { closure = Some closure; _ } ->
              apply_closure arguments path closure
          | _ ->
              typed_inline_call program analysis mode current_function path
                call_stack choices generic_calls env expression ~captured:[]
                ~ensure_closure_subtype symbol arguments))
  | Apply_value (callee, arguments) -> (
      let callee = recurse callee in
      match callee.closure with
      | Some closure -> apply_closure arguments path closure
      | None ->
          typed_error_at expression.loc
            "application head is not a function value")
  | If (condition, if_true, if_false) -> (
      let condition = recurse condition in
      let condition_term = value_term ~loc:expression.loc condition in
      let branch branch_path branch =
        typed_expr_smt_with_choices program analysis mode current_function
          (branch_path :: path) call_stack choices generic_calls env branch
      in
      let if_true = branch condition_term if_true in
      let if_false = branch (app "not" [ condition_term ]) if_false in
      let refinement =
        if if_true.refinement = if_false.refinement then if_true.refinement
        else expression.refinement
      in
      match (if_true.closure, if_false.closure) with
      | None, None ->
          make ~refinement
            (app "ite"
               [
                 condition_term;
                 value_term ~loc:expression.loc if_true;
                 value_term ~loc:expression.loc if_false;
               ])
      | Some if_true, Some if_false ->
          {
            term = "";
            refinement;
            closure =
              Some
                (Choice_closure
                   { condition = condition_term; if_true; if_false });
          }
      | _ ->
          typed_error_at expression.loc
            "conditional branches disagree on whether their result is a \
             function")
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
        | [ (_, body) ] -> value_term ~loc:expression.loc body
        | (guard, body) :: rest ->
            app "ite" [ guard; value_term ~loc:expression.loc body; tree rest ]
      in
      let closures =
        List.map (fun (guard, value) -> (guard, value.closure)) translated
      in
      if List.for_all (fun (_, closure) -> Option.is_none closure) closures then
        make ~refinement (tree translated)
      else if List.for_all (fun (_, closure) -> Option.is_some closure) closures
      then
        let rec closure_tree = function
          | [] -> typed_error_at expression.loc "empty function-valued match"
          | [ (_, Some closure) ] -> closure
          | (guard, Some if_true) :: rest ->
              Choice_closure
                { condition = guard; if_true; if_false = closure_tree rest }
          | _ -> assert false
        in
        { term = ""; refinement; closure = Some (closure_tree closures) }
      else
        typed_error_at expression.loc
          "match branches disagree on whether their result is a function"
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
    choices generic_calls env expression ~ensure_closure_subtype ~captured
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
      let previous_arity = List.length captured in
      let supplied =
        List.map
          (fun (argument : Typed_core.expr) ->
            ( typed_expr_smt_with_choices program analysis mode current_function
                path call_stack choices generic_calls env argument,
              argument.sort ))
          arguments
      in
      let captured = captured @ supplied in
      if List.length captured > List.length function_def.arguments then
        typed_error_at expression.loc "call to `%s` supplies too many arguments"
          symbol.display;
      let over_contracts =
        List.filter
          (fun (contract : Typed_core.contract) -> contract.mode = Over)
          function_def.contracts
      in
      let over_summary =
        match over_contracts with
        | [] -> None
        | [ summary ] -> Some summary
        | _ ->
            typed_error_at expression.loc
              "call to `%s` has ambiguous safety summaries" symbol.display
      in
      (match over_summary with
      | Some summary ->
          let domains = Typed_core.contract_domains summary in
          List.iteri
            (fun supplied_index _ ->
              let index = previous_arity + supplied_index in
              let parameter, domain = List.nth domains index in
              match domain with
              | Typed_core.Refined_arrow _ -> (
                  let value, _ = List.nth captured index in
                  let expected_environment =
                    List.filter_mapi
                      (fun current (value, _) ->
                        if current >= index || value.term = "" then None
                        else
                          let formal, sort =
                            List.nth function_def.arguments current
                          in
                          Some (formal.Typed_core.display, (value.term, sort)))
                      captured
                  in
                  match value.closure with
                  | Some closure ->
                      ensure_closure_subtype path expected_environment domain
                        closure
                  | None ->
                      typed_error_at expression.loc
                        "higher-order argument `%s` is not a function value"
                        parameter)
              | Refined_base domain ->
                  if String.trim domain.predicate <> "true" then (
                    let formula_env =
                      List.filter_mapi
                        (fun current (value, _) ->
                          if current > index then None
                          else
                            let formal, sort =
                              List.nth function_def.arguments current
                            in
                            Some (formal.Typed_core.display, (value.term, sort)))
                        captured
                    in
                    let predicate =
                      Typed_core.rename_identifier ~from:domain.value_name
                        ~into:parameter domain.predicate
                      |> parse_formula ~filename:summary.loc.file
                           ~loc:(location_of_span summary.loc)
                    in
                    formula_theory_symbols program.registry formula_env
                      predicate
                    |> List.iter (use_theory_symbol generic_calls);
                    add_call_side_condition generic_calls path
                      (typed_formula program.registry formula_env predicate)))
            supplied
      | None -> ());
      if List.length captured < List.length function_def.arguments then
        let specification =
          Option.map
            (fun (summary : Typed_core.contract) ->
              drop_refined_arguments (List.length captured) summary.refined_type)
            over_summary
        in
        let environment =
          List.filter_map
            (fun (((formal : Typed_core.symbol), sort), (value, _)) ->
              if value.term = "" then None
              else Some (formal.display, (value.term, sort)))
            (List.combine
               (List.filteri
                  (fun index _ -> index < List.length captured)
                  function_def.arguments)
               captured)
        in
        {
          term = "";
          refinement = expression.refinement;
          closure =
            Some
              (Direct_closure { symbol; captured; specification; environment });
        }
      else
        let function_def =
          instantiate_function_at_call_sorts ~loc:expression.loc function_def
            (List.map snd captured) expression.sort
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
              program.registry.datatypes <-
                datatype :: program.registry.datatypes)
          call_program.registry.datatypes;
        let values = List.map fst captured in
        let terms =
          List.map2
            (fun value (_, sort) ->
              match sort with
              | Typed_core.S_arrow _ ->
                  let name =
                    "closure_argument_" ^ string_of_int (List.length !choices)
                  in
                  choices := (name, sort) :: !choices;
                  name
              | _ -> value_term ~loc:expression.Typed_core.loc value)
            values function_def.arguments
        in
        let recursive =
          Function_analysis.is_recursive_edge analysis
            ~caller:current_function.Typed_core.symbol.key ~callee:symbol.key
        in
        let constructive_under_contracts =
          List.filter
            (fun (contract : Typed_core.contract) ->
              contract.mode = Under
              && (contract.witnesses <> []
                 || contract.witness_relation <> None
                 || List.for_all
                      (fun ((argument : Typed_core.symbol), _) ->
                        List.mem argument.display contract.universals)
                      function_def.arguments))
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
          let formula_env =
            List.map2
              (fun ((argument : Typed_core.symbol), sort) term ->
                (argument.display, (term, sort)))
              function_def.arguments terms
          in
          let add_termination_condition () =
            if recursive then (
              let callee_measure =
                match function_def.measure with
                | _ :: _ as measures -> measures
                | [] ->
                    typed_error_at expression.loc
                      "recursive callee `%s` needs [@refined.measure]"
                      symbol.display
              in
              let caller_measure =
                match current_function.Typed_core.measure with
                | _ :: _ as measures -> measures
                | [] ->
                    typed_error_at expression.loc
                      "recursive caller `%s` needs [@refined.measure]"
                      current_function.symbol.display
              in
              let callee_measure_term =
                List.map
                  (fun (measure : Typed_core.symbol) ->
                    List.find_map
                      (fun (((argument : Typed_core.symbol), _), term) ->
                        if argument.key = measure.key then Some term else None)
                      (List.combine function_def.arguments terms)
                    |> Option.get)
                  callee_measure
              in
              let caller_measure_term =
                List.map
                  (fun (measure : Typed_core.symbol) ->
                    match List.assoc_opt measure.key env with
                    | Some value -> value.term
                    | None -> assert false)
                  caller_measure
              in
              if List.length callee_measure <> List.length caller_measure then
                typed_error_at expression.loc
                  "recursive caller and callee have incompatible lexicographic \
                   measures";
              add_call_side_condition generic_calls path
                (termination_decrease ~loc:expression.loc function_def
                   callee_measure ~callee:callee_measure_term
                   ~caller:caller_measure_term))
          in
          add_termination_condition ();
          match Typed_core.contract_result summary with
          | Refined_arrow _ as specification ->
              let function_sort = Typed_core.refined_sort specification in
              let identity =
                "call_closure_" ^ string_of_int (List.length !choices)
              in
              choices := (identity, function_sort) :: !choices;
              {
                term = "";
                refinement = expression.refinement;
                closure =
                  Some
                    (Abstract_closure
                       {
                         specification;
                         environment = formula_env;
                         identity;
                         function_sort;
                       });
              }
          | Refined_base _ ->
              let result =
                "call_result_" ^ string_of_int (List.length !choices)
              in
              choices := (result, function_def.result) :: !choices;
              let post =
                let _, formula = contract_expressions summary in
                formula_theory_symbols program.registry
                  (("result", (result, function_def.result)) :: formula_env)
                  formula
                |> List.iter (use_theory_symbol generic_calls);
                typed_formula program.registry
                  (("result", (result, function_def.result)) :: formula_env)
                  formula
              in
              generic_calls.summary_assumptions <-
                under_path path post :: generic_calls.summary_assumptions;
              {
                term = result;
                refinement = expression.refinement;
                closure = None;
              })
        else if mode = Under && constructive_under_contracts <> [] then (
          let summary =
            match constructive_under_contracts with
            | [ summary ] -> summary
            | _ ->
                typed_error_at expression.loc
                  "call to `%s` has ambiguous constructive coverage summaries"
                  symbol.display
          in
          let existential_formals =
            List.filter
              (fun ((argument : Typed_core.symbol), _) ->
                not (List.mem argument.display summary.universals))
              function_def.arguments
          in
          let formal_names =
            List.map
              (fun ((argument : Typed_core.symbol), _) -> argument.display)
              existential_formals
          in
          if
            summary.witnesses <> []
            && List.sort String.compare (List.map fst summary.witnesses)
               <> List.sort String.compare formal_names
          then
            typed_error_at expression.loc
              "coverage summary for `%s` has incomplete witnesses"
              symbol.display;
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
          let formula_env =
            List.map2
              (fun ((formal : Typed_core.symbol), sort) term ->
                (formal.display, (term, sort)))
              function_def.arguments terms
          in
          let universal_formula_env =
            List.filter
              (fun (name, _) -> List.mem name summary.universals)
              formula_env
          in
          let witness_env = ghost_env @ result_env @ universal_formula_env in
          let parse text =
            parse_formula ~filename:summary.loc.file
              ~loc:(location_of_span summary.loc)
              text
          in
          let _, post_formula = contract_expressions summary in
          formula_theory_symbols program.registry
            (result_env @ universal_formula_env)
            post_formula
          |> List.iter (use_theory_symbol generic_calls);
          let domain_constraints =
            contract_domain_expressions summary
            |> List.map (fun (_index, domain) ->
                formula_theory_symbols program.registry formula_env domain
                |> List.iter (use_theory_symbol generic_calls);
                typed_formula program.registry formula_env domain)
          in
          let witness_constraints =
            if summary.witnesses = [] then []
            else
              List.map
                (fun (((formal : Typed_core.symbol), sort), actual) ->
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
                (List.filter_map
                   (fun (((formal : Typed_core.symbol), sort), actual) ->
                     if List.mem formal.display summary.universals then None
                     else Some ((formal, sort), actual))
                   (List.combine function_def.arguments terms))
          in
          let constraints =
            typed_formula program.registry
              (result_env @ universal_formula_env)
              post_formula
            :: domain_constraints
            @ witness_constraints
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
          if recursive then (
            let callee_measure =
              match function_def.measure with
              | _ :: _ as measures -> measures
              | [] ->
                  typed_error_at expression.loc
                    "recursive coverage callee `%s` needs [@refined.measure]"
                    symbol.display
            in
            let caller_measure =
              match current_function.Typed_core.measure with
              | _ :: _ as measures -> measures
              | [] ->
                  typed_error_at expression.loc
                    "recursive coverage caller `%s` needs [@refined.measure]"
                    current_function.symbol.display
            in
            let callee =
              List.map
                (fun (measure : Typed_core.symbol) ->
                  List.find_map
                    (fun (((argument : Typed_core.symbol), _), term) ->
                      if argument.key = measure.key then Some term else None)
                    (List.combine function_def.arguments terms)
                  |> Option.get)
                callee_measure
            in
            let caller =
              List.map
                (fun (measure : Typed_core.symbol) ->
                  (List.assoc measure.key env).term)
                caller_measure
            in
            if List.length callee_measure <> List.length caller_measure then
              typed_error_at expression.loc
                "recursive caller and callee have incompatible lexicographic \
                 measures";
            generic_calls.summary_assumptions <-
              under_path path
                (termination_decrease ~loc:expression.loc function_def
                   callee_measure ~callee ~caller)
              :: generic_calls.summary_assumptions);
          { term = result; refinement = expression.refinement; closure = None })
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
  | Var _ | Int _ | Bool _ | Lambda _ -> false
  | Tuple expressions
  | Construct (_, expressions)
  | Choose expressions
  | Apply (_, expressions)
  | Record (_, expressions) ->
      List.exists typed_has_exception expressions
  | Apply_value (callee, expressions) ->
      typed_has_exception callee || List.exists typed_has_exception expressions
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
              List.exists
                (fun (contract : Typed_core.contract) ->
                  contract.result_state <> None
                  || contract.result_references <> [])
                callee.contracts
              || check (symbol.key :: visited) callee.body)
            (List.find_opt
               (fun (callee : Typed_core.function_def) ->
                 callee.symbol.key = symbol.key)
               program.functions)
    | Apply_value (callee, arguments) ->
        check visited callee || List.exists (check visited) arguments
    | Lambda (_, body) -> check visited body
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
    | Apply_value (callee, expressions) ->
        List.fold_left collect (collect cells callee) expressions
    | Lambda (_, body) -> collect cells body
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
        | S_arrow _ | S_int | S_bool | S_unit | S_var _ -> [])
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
    | Apply_value (callee, expressions) ->
        List.fold_left collect (collect sorts callee) expressions
    | Lambda (_, body) -> collect sorts body
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
    | Apply_value (callee, expressions) ->
        List.fold_left collect (collect sorts callee) expressions
    | Lambda (parameters, body) ->
        let sorts =
          List.fold_left (fun sorts (_, sort) -> sort :: sorts) sorts parameters
        in
        collect sorts body
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

let use_returned_reference_theory generic_calls registry sort =
  Ownership.use_returned_reference_theory
    (use_theory_symbol generic_calls)
    registry sort

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
    | Apply_value (callee, expressions) ->
        List.fold_left (collect visited)
          (collect visited outcomes callee)
          expressions
    | Lambda (_, body) -> collect visited outcomes body
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
  let bind relation continuation =
    List.concat_map
      (fun (prior : R.path) ->
        let previous = generic_calls.side_conditions in
        generic_calls.side_conditions <- [];
        let result = R.bind [ prior ] continuation in
        (* Only checks created by the continuation may use this outcome's
           postcondition. The call's own preconditions remain outside it. *)
        generic_calls.side_conditions <-
          List.map (under_path [ prior.guard ]) generic_calls.side_conditions
          @ previous;
        result)
      relation
  in
  let continuation_counter = ref 0 in
  let allocated_references =
    ref
      (typed_reference_arguments function_def
      |> List.filter_map (fun (_, key, sort) ->
          Option.map (fun value -> (value.term, sort)) (List.assoc_opt key env))
      )
  in
  let is_arrow = function Typed_core.S_arrow _ -> true | _ -> false in
  let is_global_function symbol =
    List.exists
      (fun (callee : Typed_core.function_def) ->
        callee.symbol.key = symbol.Typed_core.key)
      program.Typed_core.functions
  in
  let global_function symbol =
    List.find_opt
      (fun (callee : Typed_core.function_def) ->
        callee.symbol.key = symbol.Typed_core.key)
      program.Typed_core.functions
  in
  let residual_application (expression : Typed_core.expr) =
    match expression.desc with
    | Var global ->
        Option.map (fun callee -> (callee, [])) (global_function global)
    | Apply (global, arguments) -> (
        match global_function global with
        | Some callee when List.length arguments < List.length callee.arguments
          ->
            Some (callee, arguments)
        | Some _ | None -> None)
    | _ -> None
  in
  let rec substitute_closure target replacement (expression : Typed_core.expr) =
    let recurse = substitute_closure target replacement in
    let desc =
      match expression.desc with
      | Var symbol when symbol.key = target -> replacement.Typed_core.desc
      | Apply (symbol, arguments) when symbol.key = target ->
          Apply_value (replacement, List.map recurse arguments)
      | (Var _ | Int _ | Bool _ | Deref _) as desc -> desc
      | Apply (symbol, arguments) -> Apply (symbol, List.map recurse arguments)
      | Apply_value (callee, arguments) ->
          Apply_value (recurse callee, List.map recurse arguments)
      | Lambda (parameters, body) -> Lambda (parameters, recurse body)
      | Tuple expressions -> Tuple (List.map recurse expressions)
      | Construct (constructor, expressions) ->
          Construct (constructor, List.map recurse expressions)
      | Record (constructor, expressions) ->
          Record (constructor, List.map recurse expressions)
      | Choose expressions -> Choose (List.map recurse expressions)
      | If (condition, if_true, if_false) ->
          If (recurse condition, recurse if_true, recurse if_false)
      | Let (symbol, value, body) -> Let (symbol, recurse value, recurse body)
      | Match (scrutinee, cases) ->
          Match
            ( recurse scrutinee,
              List.map (fun (pattern, body) -> (pattern, recurse body)) cases )
      | Field (constructor, index, record) ->
          Field (constructor, index, recurse record)
      | Raise (exception_, payload) ->
          Raise (exception_, Option.map recurse payload)
      | Try (body, cases) ->
          Try
            ( recurse body,
              List.map
                (fun (pattern, handler) -> (pattern, recurse handler))
                cases )
      | Ref (sort, initial) -> Ref (sort, recurse initial)
      | Let_ref (symbol, sort, initial, body) ->
          Let_ref (symbol, sort, recurse initial, recurse body)
      | Assign (symbol, value) -> Assign (symbol, recurse value)
      | Sequence (first, second) -> Sequence (recurse first, recurse second)
      | Perform (operation, payload) ->
          Perform (operation, Option.map recurse payload)
      | Handle (body, handlers) ->
          let rec action = function
            | Typed_core.Abort body -> Typed_core.Abort (recurse body)
            | Resume value -> Resume (recurse value)
            | Conditional (condition, if_true, if_false) ->
                Conditional (recurse condition, action if_true, action if_false)
          in
          Handle
            ( recurse body,
              List.map
                (fun (operation, payload, handler) ->
                  (operation, payload, action handler))
                handlers )
    in
    { expression with desc }
  in
  let rec normalize_residual_closures (expression : Typed_core.expr) =
    let normalize = normalize_residual_closures in
    let rebuild desc = { expression with desc } in
    match expression.desc with
    | Let (symbol, value, body) when is_arrow value.sort -> (
        let value : Typed_core.expr = normalize value in
        match value.desc with
        | Lambda _ -> substitute_closure symbol.key value body |> normalize
        | _ -> rebuild (Let (symbol, value, normalize body)))
    | Apply_value (callee, arguments) -> (
        let callee = normalize callee in
        let arguments = List.map normalize arguments in
        match callee.desc with
        | Lambda (parameters, body) ->
            let rec beta parameters arguments =
              match (parameters, arguments) with
              | [], [] -> normalize body
              | [], arguments ->
                  rebuild (Apply_value (normalize body, arguments))
              | parameters, [] -> rebuild (Lambda (parameters, normalize body))
              | (parameter, _) :: parameters, argument :: arguments ->
                  let result = beta parameters arguments in
                  {
                    desc = Let (parameter, argument, result);
                    sort = result.sort;
                    refinement = result.refinement;
                    loc = expression.loc;
                  }
            in
            beta parameters arguments
        | Var symbol when is_global_function symbol ->
            rebuild (Apply (symbol, arguments))
        | Apply (symbol, _captured) when is_global_function symbol ->
            rebuild (Apply_value (callee, arguments))
        | _ -> rebuild (Apply_value (callee, arguments)))
    | Lambda (parameters, body) -> rebuild (Lambda (parameters, normalize body))
    | Var _ | Int _ | Bool _ | Deref _ -> expression
    | Apply (symbol, arguments) ->
        rebuild (Apply (symbol, List.map normalize arguments))
    | Tuple expressions -> rebuild (Tuple (List.map normalize expressions))
    | Construct (constructor, expressions) ->
        rebuild (Construct (constructor, List.map normalize expressions))
    | Record (constructor, expressions) ->
        rebuild (Record (constructor, List.map normalize expressions))
    | Choose expressions -> rebuild (Choose (List.map normalize expressions))
    | If (condition, if_true, if_false) ->
        rebuild
          (If (normalize condition, normalize if_true, normalize if_false))
    | Let (symbol, value, body) ->
        rebuild (Let (symbol, normalize value, normalize body))
    | Match (scrutinee, cases) ->
        rebuild
          (Match
             ( normalize scrutinee,
               List.map (fun (pattern, body) -> (pattern, normalize body)) cases
             ))
    | Field (constructor, index, record) ->
        rebuild (Field (constructor, index, normalize record))
    | Raise (exception_, payload) ->
        rebuild (Raise (exception_, Option.map normalize payload))
    | Try (body, cases) ->
        rebuild
          (Try
             ( normalize body,
               List.map
                 (fun (pattern, handler) -> (pattern, normalize handler))
                 cases ))
    | Ref (sort, initial) -> rebuild (Ref (sort, normalize initial))
    | Let_ref (symbol, sort, initial, body) ->
        rebuild (Let_ref (symbol, sort, normalize initial, normalize body))
    | Assign (symbol, value) -> rebuild (Assign (symbol, normalize value))
    | Sequence (first, second) ->
        rebuild (Sequence (normalize first, normalize second))
    | Perform (operation, payload) ->
        rebuild (Perform (operation, Option.map normalize payload))
    | Handle (body, handlers) ->
        let rec action = function
          | Typed_core.Abort body -> Typed_core.Abort (normalize body)
          | Resume value -> Resume (normalize value)
          | Conditional (condition, if_true, if_false) ->
              Conditional (normalize condition, action if_true, action if_false)
        in
        rebuild
          (Handle
             ( normalize body,
               List.map
                 (fun (operation, payload, handler) ->
                   (operation, payload, action handler))
                 handlers ))
  in
  let expression = normalize_residual_closures expression in
  let latent_effectful_function (expression : Typed_core.expr) =
    match expression.desc with
    | Lambda (_, body) -> typed_has_exception body
    | _ -> false
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
    | Apply_value (callee, arguments)
      when Option.is_some (residual_application callee) ->
        let _closure =
          typed_expr_smt_with_choices program analysis mode function_def path []
            choices generic_calls env callee
        in
        let function_def, captured = Option.get (residual_application callee) in
        let application =
          {
            expression with
            desc = Apply (function_def.symbol, captured @ arguments);
          }
        in
        translate env state path application continuation
    | Apply (symbol, arguments)
      when List.exists latent_effectful_function arguments ->
        let callee =
          List.find_opt
            (fun (callee : Typed_core.function_def) ->
              callee.symbol.key = symbol.key)
            program.Typed_core.functions
          |> function
          | Some callee -> callee
          | None ->
              typed_error_at expression.loc
                "effectful higher-order call `%s` needs a local definition"
                symbol.display
        in
        if
          Function_analysis.is_recursive_edge analysis
            ~caller:function_def.symbol.key ~callee:callee.symbol.key
        then
          typed_error_at expression.loc
            "recursive effectful higher-order call `%s` is unsupported"
            symbol.display;
        if List.length arguments <> List.length callee.arguments then
          typed_error_at expression.loc
            "effectful higher-order call `%s` must be fully applied"
            symbol.display;
        let summary =
          match
            List.filter
              (fun (contract : Typed_core.contract) -> contract.mode = Over)
              callee.contracts
          with
          | [ summary ] -> summary
          | [] ->
              typed_error_at expression.loc
                "effectful higher-order call `%s` needs one safety summary"
                symbol.display
          | _ ->
              typed_error_at expression.loc
                "effectful higher-order call `%s` has ambiguous safety \
                 summaries"
                symbol.display
        in
        let rec check_arguments expected_environment domains arguments =
          match (domains, arguments) with
          | [], [] -> ()
          | (parameter, domain) :: domains, argument :: arguments ->
              (match domain with
              | Typed_core.Refined_arrow _ ->
                  verify_effectful_closure env state path expected_environment
                    domain argument
              | Refined_base base ->
                  let value =
                    typed_expr_smt_with_choices program analysis mode
                      function_def path [] choices generic_calls env argument
                  in
                  let predicate =
                    typed_refinement_predicate program generic_calls
                      ~loc:argument.loc expected_environment base value.term
                  in
                  generic_calls.side_conditions <-
                    under_path path predicate :: generic_calls.side_conditions);
              let value =
                match domain with
                | Typed_core.Refined_base _ ->
                    typed_expr_smt_with_choices program analysis mode
                      function_def path [] choices generic_calls env argument
                | Refined_arrow _ ->
                    {
                      term =
                        "higher_order_argument_"
                        ^ string_of_int (List.length !choices);
                      refinement = None;
                      closure = None;
                    }
              in
              check_arguments
                ((parameter, (value.term, Typed_core.refined_sort domain))
                :: expected_environment)
                domains arguments
          | _ -> invalid_arg "effectful higher-order contract arity mismatch"
        in
        check_arguments [] (Typed_core.contract_domains summary) arguments;
        let inlined =
          List.fold_left2
            (fun body ((formal : Typed_core.symbol), _) argument ->
              substitute_closure formal.key argument body)
            callee.body callee.arguments arguments
          |> normalize_residual_closures
        in
        translate env state path inlined continuation
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
                  | _ :: _ as measures -> measures
                  | [] ->
                      typed_error_at expression.loc
                        "recursive outcome callee `%s` needs [@refined.measure]"
                        symbol.display
                in
                let caller_measure =
                  match function_def.Typed_core.measure with
                  | _ :: _ as measures -> measures
                  | [] ->
                      typed_error_at expression.loc
                        "recursive outcome caller `%s` needs [@refined.measure]"
                        function_def.symbol.display
                in
                let callee_term =
                  List.map
                    (fun (measure : Typed_core.symbol) ->
                      List.find_map
                        (fun (((formal : Typed_core.symbol), _), term) ->
                          if formal.key = measure.key then Some term else None)
                        (List.combine callee.arguments terms)
                      |> Option.get)
                    callee_measure
                in
                let caller_term =
                  List.map
                    (fun (measure : Typed_core.symbol) ->
                      match List.assoc_opt measure.key env with
                      | Some value -> value.term
                      | None -> assert false)
                    caller_measure
                in
                if List.length callee_measure <> List.length caller_measure then
                  typed_error_at expression.loc
                    "recursive caller and callee have incompatible \
                     lexicographic measures";
                and_
                  [
                    termination_decrease ~loc:expression.loc callee
                      callee_measure ~callee:callee_term ~caller:caller_term;
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
              let universal_formula_env =
                List.filter
                  (fun (name, _) -> List.mem name summary.universals)
                  call_formula_env
              in
              let value_formals =
                List.combine callee.arguments terms
                |> List.filter_map
                     (fun (((formal : Typed_core.symbol), sort), term) ->
                       if List.mem formal.display summary.universals then None
                       else
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
              let domain_guards =
                contract_domain_expressions summary
                |> List.map (fun (_index, domain) ->
                    formula_theory_symbols program.registry call_formula_env
                      domain
                    |> List.iter (use_theory_symbol generic_calls);
                    typed_formula program.registry call_formula_env domain)
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
              let required_region_guards =
                summary.requires_regions
                |> List.concat_map (fun (formal_name, region) ->
                    let index =
                      List.find_mapi
                        (fun index ((formal : Typed_core.symbol), _) ->
                          if formal.display = formal_name then Some index
                          else None)
                        callee.arguments
                      |> Option.get
                    in
                    let root = List.nth terms index in
                    let _, root_sort = List.nth callee.arguments index in
                    region_frontier_specs program summary.mode
                      ~loc:expression.loc region ~root_sort ~root
                    |> List.map
                         (fun (path, predicate, (owner : Source_span.t)) ->
                           use_returned_reference_theory generic_calls
                             program.registry root_sort;
                           let predicate =
                             parse_formula ~filename:owner.file
                               ~loc:(location_of_span owner) predicate
                           in
                           let state_env =
                             [
                               ( "identity",
                                 ( path.identity,
                                   reference_sort path.content_sort ) );
                               ( "value",
                                 ( heap_select state path.identity
                                     path.content_sort,
                                   path.content_sort ) );
                             ]
                           in
                           formula_theory_symbols program.registry state_env
                             predicate
                           |> List.iter (use_theory_symbol generic_calls);
                           app "=>"
                             [
                               path.guard;
                               typed_formula program.registry state_env
                                 predicate;
                             ]))
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
                      returned_reference_paths
                        ~recursive_frontier:summary.result_recursive
                        program.registry ~result_sort:callee.result ~result
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
                validate_result_reference_permissions ~loc:expression.loc
                  summary
                  (List.map (fun path -> path.path) owned_paths);
                let ( owned_targets,
                      owned_freshness,
                      owned_final_state,
                      owned_updates ) =
                  List.fold_left
                    (fun (targets, guards, final_state, updates) path ->
                      let content =
                        fresh "call_reachable_state_" path.content_sort
                      in
                      let transfer =
                        result_reference_is_transfer summary path.path
                      in
                      let borrow_guards =
                        if transfer then []
                        else
                          let candidates =
                            reference_formals
                            |> List.filter_map (fun (name, _, sort) ->
                                if
                                  typed_smt_sort sort
                                  = typed_smt_sort path.content_sort
                                then
                                  let actual, _ = actual_cell name in
                                  Some (name, actual, sort)
                                else None)
                          in
                          app "=>"
                            [
                              path.guard;
                              or_
                                (List.map
                                   (fun (_name, actual, _sort) ->
                                     app "=" [ path.identity; actual ])
                                   candidates);
                            ]
                          :: List.filter_map
                               (fun (name, actual, sort) ->
                                 if
                                   List.mem name summary.modifies
                                   || List.mem_assoc name summary.state
                                 then None
                                 else
                                   Some
                                     (app "=>"
                                        [
                                          and_
                                            [
                                              path.guard;
                                              app "=" [ path.identity; actual ];
                                            ];
                                          app "="
                                            [
                                              content;
                                              heap_select state actual sort;
                                            ];
                                        ]))
                               candidates
                      in
                      let freshness =
                        if not transfer then []
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
                        borrow_guards @ freshness @ guards,
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
                  @ List.concat_map
                      (fun (path, content, _predicate) ->
                        [
                          ( returned_reference_value_name path.path,
                            (content, path.content_sort) );
                          ( returned_reference_identity_name path.path,
                            (path.identity, reference_sort path.content_sort) );
                        ])
                      owned_targets
                  @ List.map
                      (fun (name, _, sort, target, _) -> (name, (target, sort)))
                      state_targets
                  @ universal_formula_env
                in
                let ghost_env = fresh_ghosts "call_ghost_" in
                let witness_env = ghost_env @ public_target_env in
                let relation_env =
                  witness_env @ call_formula_env @ old_reference_env
                in
                let _, post = contract_expressions summary in
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
                        ( "identity",
                          (path.identity, reference_sort path.content_sort) )
                        :: ("value", (content, path.content_sort))
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
                          @ alias_guards @ required_region_guards
                          @ domain_guards
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
                    @ payload_env @ universal_formula_env
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
                      @ required_region_guards @ domain_guards
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
              bind (List.rev !paths) continuation)
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
              let pre_formulas, _ = contract_expressions summary in
              List.iter (mark formula_env) pre_formulas;
              generic_calls.side_conditions <-
                under_path path
                  (and_
                     (List.map
                        (typed_formula program.registry formula_env)
                        pre_formulas))
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
              let required_region_guards =
                summary.requires_regions
                |> List.concat_map (fun (formal_name, region) ->
                    let index =
                      List.find_mapi
                        (fun index ((formal : Typed_core.symbol), _) ->
                          if formal.display = formal_name then Some index
                          else None)
                        callee.arguments
                      |> Option.get
                    in
                    let root = List.nth terms index in
                    let _, root_sort = List.nth callee.arguments index in
                    region_frontier_specs program summary.mode
                      ~loc:expression.loc region ~root_sort ~root
                    |> List.map
                         (fun (path, predicate, (owner : Source_span.t)) ->
                           use_returned_reference_theory generic_calls
                             program.registry root_sort;
                           let predicate =
                             parse_formula ~filename:owner.file
                               ~loc:(location_of_span owner) predicate
                           in
                           let state_env =
                             [
                               ( "identity",
                                 ( path.identity,
                                   reference_sort path.content_sort ) );
                               ( "value",
                                 ( heap_select state path.identity
                                     path.content_sort,
                                   path.content_sort ) );
                             ]
                           in
                           mark state_env predicate;
                           app "=>"
                             [
                               path.guard;
                               typed_formula program.registry state_env
                                 predicate;
                             ]))
              in
              generic_calls.side_conditions <-
                List.rev_append
                  (List.map (under_path path) required_region_guards)
                  generic_calls.side_conditions;
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
              let _, post_formula = contract_expressions summary in
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
                    returned_reference_paths
                      ~recursive_frontier:summary.result_recursive
                      program.registry ~result_sort:callee.result ~result
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
              validate_result_reference_permissions ~loc:expression.loc summary
                expected_paths;
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
                      ( "identity",
                        (path.identity, reference_sort path.content_sort) )
                      :: ("value", (content, path.content_sort))
                      :: result_env
                    in
                    mark state_env predicate;
                    let predicate =
                      app "=>"
                        [
                          path.guard;
                          typed_formula program.registry state_env predicate;
                        ]
                    in
                    let transfer =
                      result_reference_is_transfer summary path.path
                    in
                    let borrow_guards =
                      if transfer then []
                      else
                        let candidates =
                          reference_formals
                          |> List.filter_map (fun (name, _, sort) ->
                              if
                                typed_smt_sort sort
                                = typed_smt_sort path.content_sort
                              then
                                let actual, _ = actual_cell name in
                                Some (name, actual, sort)
                              else None)
                        in
                        app "=>"
                          [
                            path.guard;
                            or_
                              (List.map
                                 (fun (_name, actual, _sort) ->
                                   app "=" [ path.identity; actual ])
                                 candidates);
                          ]
                        :: List.filter_map
                             (fun (name, actual, sort) ->
                               if
                                 List.mem name summary.modifies
                                 || List.mem_assoc name summary.state
                               then None
                               else
                                 Some
                                   (app "=>"
                                      [
                                        and_
                                          [
                                            path.guard;
                                            app "=" [ path.identity; actual ];
                                          ];
                                        app "="
                                          [
                                            content;
                                            heap_select state actual sort;
                                          ];
                                      ]))
                             candidates
                    in
                    let freshness =
                      if not transfer then []
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
                    ( ((predicate :: borrow_guards) @ freshness) @ guards,
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
              bind ((normal :: exceptional) @ performed) continuation)
    | Choose [ left; right ]
      when left.Typed_core.sort = expression.sort
           && right.Typed_core.sort = expression.sort ->
        translate env state path left continuation
        @ translate env state path right continuation
    | Choose arguments ->
        let rec evaluate state = function
          | [] ->
              let name =
                "choice_value_" ^ string_of_int (List.length !choices)
              in
              choices := (name, expression.sort) :: !choices;
              continuation name state
          | argument :: arguments ->
              translate env state path argument (fun _ state ->
                  evaluate state arguments)
        in
        evaluate state arguments
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
                        ( binder.key,
                          { term = payload; refinement = None; closure = None }
                        )
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
        bind (discharge (translate env state path body boundary)) continuation
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
    | Let (symbol, value, body)
      when is_arrow value.sort && Option.is_some (residual_application value) ->
        let closure =
          typed_expr_smt_with_choices program analysis mode function_def path []
            choices generic_calls env value
        in
        if Option.is_none closure.closure then
          typed_error_at value.loc
            "function-valued binding did not produce a residual closure";
        let body =
          substitute_closure symbol.key value body
          |> normalize_residual_closures
        in
        translate env state path body continuation
    | Let (symbol, value, body) ->
        translate env state path value (fun value state ->
            translate
              ((symbol.key, { term = value; refinement = None; closure = None })
              :: env)
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
                        ( binder.key,
                          { term = payload; refinement = None; closure = None }
                        )
                        :: env
                    | Exn (_, None), _ | Exn_any, _ -> env
                    | Exn (_, Some _), None ->
                        typed_error_at expression.loc
                          "exception handler expected a payload"
                  in
                  translate handler_env state path handler boundary
              | None -> R.raise_ ~state exception_)
        in
        bind handled continuation
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
              ( symbol.key,
                { term = identity; refinement = None; closure = None } )
              :: env
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
        bind (R.return ~state (app "select" [ heap; identity ])) continuation
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
  and verify_effectful_closure env state path expected_environment expected
      (expression : Typed_core.expr) =
    let parameters, body =
      match expression.desc with
      | Lambda (parameters, body) -> (parameters, body)
      | _ ->
          typed_error_at expression.loc
            "effectful higher-order argument is not an anonymous/local closure"
    in
    let rec bind expected_environment local_environment domain_guards parameters
        expected =
      match (parameters, expected) with
      | [], Typed_core.Refined_base result ->
          let relation =
            translate local_environment state (domain_guards @ path) body
              (fun value state -> R.return ~state value)
          in
          let obligations =
            List.map
              (fun (outcome : R.path) ->
                match outcome.outcome with
                | Return value ->
                    let post =
                      typed_refinement_predicate program generic_calls
                        ~loc:body.loc expected_environment result value
                    in
                    app "=>" [ outcome.guard; post ]
                | Raised _ | Performed _ -> app "not" [ outcome.guard ])
              relation
          in
          generic_calls.side_conditions <-
            under_path path (app "=>" [ and_ domain_guards; and_ obligations ])
            :: generic_calls.side_conditions
      | ( (parameter, sort) :: parameters,
          Typed_core.Refined_arrow
            { parameter = expected_parameter; domain; codomain } ) -> (
          match domain with
          | Typed_core.Refined_arrow _ ->
              typed_error_at expression.loc
                "effectful local closures with function-valued parameters are \
                 not yet supported"
          | Refined_base base ->
              let input =
                "closure_check_input_" ^ string_of_int (List.length !choices)
              in
              choices := (input, sort) :: !choices;
              let guard =
                typed_refinement_predicate program generic_calls
                  ~loc:expression.loc expected_environment base input
              in
              bind
                ((expected_parameter, (input, sort)) :: expected_environment)
                (( parameter.Typed_core.key,
                   { term = input; refinement = None; closure = None } )
                :: local_environment)
                (guard :: domain_guards) parameters codomain)
      | [], Typed_core.Refined_arrow _ ->
          typed_error_at expression.loc
            "effectful local closure returns a function before its safety type \
             is fully observed"
      | _ ->
          typed_error_at expression.loc
            "effectful local closure arity does not match its safety type"
    in
    bind expected_environment env [] parameters expected
  in
  let boundary value state = R.return ~state value in
  let relation =
    translate env initial_state [] expression boundary
    |> List.map (fun (path : R.path) -> { path with initial_state })
  in
  (relation, List.rev !choices, generic_calls)

let typed_collect_sorts ?(extra_sorts = []) program function_def =
  let module Set = Set.Make (String) in
  let rec closed = function
    | Typed_core.S_var _ -> false
    | S_tuple sorts | S_app (_, sorts) -> List.for_all closed sorts
    | S_arrow (domain, codomain) -> closed domain && closed codomain
    | S_int | S_bool | S_unit -> true
  in
  let rec add set sort =
    let set = Set.add (typed_smt_sort sort) set in
    match sort with
    | Typed_core.S_tuple sorts | S_app (_, sorts) ->
        List.fold_left add set sorts
    | S_arrow (domain, codomain) -> add (add set domain) codomain
    | S_int | S_bool | S_unit | S_var _ -> set
  in
  let set =
    List.fold_left
      (fun set (_, sort) -> add set sort)
      Set.empty function_def.Typed_core.arguments
  in
  let set = List.fold_left add (add set function_def.result) extra_sorts in
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
        List.fold_left
          (fun set (_, sort) -> add set sort)
          set
          (List.map (fun (_, name, sort) -> (name, sort)) axiom.binders))
      set program.registry.axioms
  in
  let set =
    List.fold_left
      (fun set (lemma : Typed_core.axiom) ->
        List.fold_left
          (fun set (_, sort) -> add set sort)
          set
          (List.map (fun (_, name, sort) -> (name, sort)) lemma.binders))
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

let typed_collect_sort_values ?(extra_sorts = []) program function_def =
  let values = Hashtbl.create 32 in
  let rec closed = function
    | Typed_core.S_var _ -> false
    | S_tuple sorts | S_app (_, sorts) -> List.for_all closed sorts
    | S_arrow (domain, codomain) -> closed domain && closed codomain
    | S_int | S_bool | S_unit -> true
  in
  let rec add sort =
    Hashtbl.replace values (typed_smt_sort sort) sort;
    match sort with
    | Typed_core.S_tuple sorts | S_app (_, sorts) -> List.iter add sorts
    | S_arrow (domain, codomain) ->
        add domain;
        add codomain
    | S_int | S_bool | S_unit | S_var _ -> ()
  in
  List.iter (fun (_, sort) -> add sort) function_def.Typed_core.arguments;
  add function_def.result;
  List.iter add extra_sorts;
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
      List.iter
        (fun (_, sort) -> add sort)
        (List.map (fun (_, name, sort) -> (name, sort)) axiom.binders))
    program.registry.axioms;
  List.iter
    (fun (lemma : Typed_core.axiom) ->
      List.iter
        (fun (_, sort) -> add sort)
        (List.map (fun (_, name, sort) -> (name, sort)) lemma.binders))
    program.registry.checked_lemmas;
  Hashtbl.fold (fun _ sort result -> sort :: result) values []

let typed_datatype_prelude ?(extra_sorts = []) program function_def =
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
  let native_datatypes, axiomatized_datatypes =
    List.partition
      (fun (datatype : Typed_core.datatype) -> datatype.native_smt)
      program.registry.datatypes
  in
  let sort_values =
    typed_collect_sort_values ~extra_sorts program function_def
  in
  let tuple_sorts =
    List.filter_map
      (function
        | Typed_core.S_tuple elements as sort -> Some (sort, elements)
        | _ -> None)
      sort_values
  in
  let tuple_sort_names =
    List.map (fun (sort, _) -> typed_smt_sort sort) tuple_sorts
  in
  let collected_sorts = typed_collect_sorts ~extra_sorts program function_def in
  collected_sorts
  |> List.iter (fun sort ->
      if
        sort <> "Int" && sort <> "Bool"
        && (not (List.mem sort datatype_sort_names))
        && not (List.mem sort tuple_sort_names)
      then line "(declare-sort %s 0)" sort);
  if List.mem "Unit" collected_sorts then line "(declare-const unit Unit)";
  List.iter
    (fun (datatype : Typed_core.datatype) ->
      line "(declare-sort %s 0)" (typed_smt_sort datatype.owner))
    axiomatized_datatypes;
  (match native_datatypes with
  | [] -> ()
  | datatypes ->
      let sort_declarations =
        String.concat " "
          (List.map
             (fun (datatype : Typed_core.datatype) ->
               Printf.sprintf "(%s 0)" (typed_smt_sort datatype.owner))
             datatypes)
      in
      let datatype_declarations =
        String.concat " "
          (List.map
             (fun (datatype : Typed_core.datatype) ->
               "("
               ^ String.concat " "
                   (List.map
                      (fun (constructor : Typed_core.constructor) ->
                        let fields =
                          List.mapi
                            (fun index sort ->
                              Printf.sprintf "(%s %s)"
                                (typed_selector constructor index)
                                (typed_smt_sort sort))
                            constructor.arguments
                        in
                        "("
                        ^ typed_constructor_name constructor
                        ^ (match fields with
                          | [] -> ""
                          | _ -> " " ^ String.concat " " fields)
                        ^ ")")
                      datatype.constructors)
               ^ ")")
             datatypes)
      in
      line "(declare-datatypes (%s) (%s))" sort_declarations
        datatype_declarations;
      List.iter
        (fun (datatype : Typed_core.datatype) ->
          let result = typed_smt_sort datatype.owner in
          List.iter
            (fun (constructor : Typed_core.constructor) ->
              line "(define-fun %s ((value %s)) Bool ((_ is %s) value))"
                (typed_recognizer constructor)
                result
                (typed_constructor_name constructor))
            datatype.constructors)
        datatypes);
  (match tuple_sorts with
  | [] -> ()
  | tuples ->
      let sort_declarations =
        String.concat " "
          (List.map
             (fun (sort, _) -> Printf.sprintf "(%s 0)" (typed_smt_sort sort))
             tuples)
      in
      let datatype_declarations =
        String.concat " "
          (List.map
             (fun (sort, elements) ->
               let fields =
                 List.mapi
                   (fun index element ->
                     Printf.sprintf "(%s %s)"
                       (typed_tuple_selector sort index)
                       (typed_smt_sort element))
                   elements
               in
               Printf.sprintf "((%s%s))"
                 (typed_tuple_constructor sort)
                 (match fields with
                 | [] -> ""
                 | _ -> " " ^ String.concat " " fields))
             tuples)
      in
      line "(declare-datatypes (%s) (%s))" sort_declarations
        datatype_declarations);
  sort_values |> List.iter (function Typed_core.S_tuple _ -> () | _ -> ());
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
        (List.map (fun (_, name, sort) -> (name, sort)) axiom.binders)
    in
    let body = typed_formula ~scope:axiom.scope program.registry env formula in
    let assertion =
      List.fold_right
        (fun (quantifier, name, sort) body ->
          let quantifier =
            match quantifier with
            | Typed_core.Forall -> "forall"
            | Exists -> "exists"
          in
          let binder =
            Printf.sprintf "((%s %s))" (smt_identifier name)
              (typed_smt_sort sort)
          in
          app quantifier [ binder; body ])
        axiom.binders body
    in
    line "; %s: %s" provenance axiom.axiom_name;
    line "(assert %s)" assertion
  in
  List.iter
    (fun (datatype : Typed_core.datatype) ->
      let result = typed_smt_sort datatype.owner in
      List.iter
        (fun (constructor : Typed_core.constructor) ->
          line "(declare-fun %s (%s) %s)"
            (typed_constructor_name constructor)
            (String.concat " " (List.map typed_smt_sort constructor.arguments))
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
    axiomatized_datatypes;
  List.iter
    (fun (datatype : Typed_core.datatype) ->
      let result = typed_smt_sort datatype.owner in
      List.iter
        (fun (constructor : Typed_core.constructor) ->
          let arguments =
            List.mapi
              (fun index sort -> ("a" ^ string_of_int index, sort))
              constructor.arguments
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
              if other.symbol.key <> constructor.symbol.key then
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
              constructor.arguments
          in
          let rebuilt =
            if fields = [] then typed_constructor_name constructor
            else app (typed_constructor_name constructor) fields
          in
          line "(assert (forall ((v %s)) (=> (%s v) (= v %s))))" result
            (typed_recognizer constructor)
            rebuilt)
        datatype.constructors)
    axiomatized_datatypes;
  List.rev program.registry.axioms |> List.iter (emit_statement "trusted axiom");
  List.rev program.registry.checked_lemmas
  |> List.iter (emit_statement "checked lemma");
  Buffer.contents buffer
