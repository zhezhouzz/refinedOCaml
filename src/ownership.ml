open Refined_ir
open Refined_common
open Vc_logic

type returned_reference_path = {
  path : string;
  identity : string;
  content_sort : Typed_core.sort;
  guard : string;
}

let returned_reference_value_name path = "result_value_" ^ smt_identifier path

let returned_reference_identity_name path =
  "result_identity_" ^ smt_identifier path

let result_reference_is_transfer (contract : Typed_core.contract) path =
  List.mem path contract.result_fresh_references
  || List.assoc_opt path contract.result_reference_permissions = Some "transfer"

let validate_result_reference_permissions ~loc (contract : Typed_core.contract)
    expected_paths =
  let permissions = List.map fst contract.result_reference_permissions in
  if
    List.length permissions
    <> List.length (List.sort_uniq String.compare permissions)
  then
    typed_error_at loc
      "result_reference_permissions must name each path at most once";
  List.iter
    (fun (path, permission) ->
      if not (List.mem path expected_paths) then
        typed_error_at loc
          "result_reference_permissions names unknown path `%s`" path;
      if permission <> "borrow" && permission <> "transfer" then
        typed_error_at loc "reference permission must be `borrow` or `transfer`";
      if permission = "borrow" && List.mem path contract.result_fresh_references
      then
        typed_error_at loc
          "fresh reference path `%s` cannot have borrow permission" path)
    contract.result_reference_permissions

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

let returned_reference_paths ?(recursive_frontier = false) registry ~result_sort
    ~result =
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
                  if recursive_frontier then Ok []
                  else if sort_reaches_reference registry sort then
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

let use_returned_reference_theory use_symbol registry sort =
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
                      use_symbol constructor.symbol.key;
                      List.iter (visit (name :: visited)) constructor.arguments)
                    datatype.constructors)
        | S_int | S_bool | S_unit | S_var _ -> ())
  in
  visit [] sort

type region_definition = {
  region_name : string;
  region_function : Typed_core.function_def;
  region_contract : Typed_core.contract;
}

let region_definitions (program : Typed_core.program) mode =
  program.functions
  |> List.concat_map (fun function_def ->
      function_def.Typed_core.contracts
      |> List.filter_map (fun contract ->
          match contract.Typed_core.result_region with
          | Some region_name when contract.mode = mode ->
              Some
                {
                  region_name;
                  region_function = function_def;
                  region_contract = contract;
                }
          | _ -> None))

let find_region_definition program mode ~loc name =
  let definitions =
    region_definitions program mode
    |> List.filter (fun definition -> definition.region_name = name)
  in
  match definitions with
  | [] -> typed_error_at loc "unknown ownership region `%s`" name
  | definition :: rest ->
      let compatible candidate =
        typed_smt_sort candidate.region_function.result
        = typed_smt_sort definition.region_function.result
        && candidate.region_contract.result_recursive
           = definition.region_contract.result_recursive
        && candidate.region_contract.result_references
           = definition.region_contract.result_references
        && candidate.region_contract.result_reference_permissions
           = definition.region_contract.result_reference_permissions
        && candidate.region_contract.result_fresh_references
           = definition.region_contract.result_fresh_references
      in
      if not (List.for_all compatible rest) then
        typed_error_at loc "ownership region `%s` has incompatible definitions"
          name;
      definition

type region_binding = { region : string; origin : string }

type region_linear_state = {
  region_env : (string * region_binding) list;
  consumed_origins : string list;
  borrowed_origins : string list;
}

let validate_region_contracts (program : Typed_core.program)
    (function_def : Typed_core.function_def) (contract : Typed_core.contract) =
  let mode = contract.mode in
  let argument_by_name =
    List.map
      (fun ((symbol : Typed_core.symbol), sort) ->
        (symbol.display, (symbol, sort)))
      function_def.arguments
  in
  let initial_regions =
    List.map
      (fun (name, region) ->
        let symbol, sort =
          match List.assoc_opt name argument_by_name with
          | Some argument -> argument
          | None ->
              typed_error_at contract.loc
                "requires_regions names unknown parameter `%s`" name
        in
        let definition =
          find_region_definition program mode ~loc:contract.loc region
        in
        if
          typed_smt_sort sort
          <> typed_smt_sort definition.region_function.result
        then
          typed_error_at contract.loc
            "region `%s` has the wrong sort for parameter `%s`" region name;
        (symbol.key, { region; origin = "argument:" ^ symbol.key }))
      contract.requires_regions
  in
  List.iter
    (fun name ->
      if not (List.mem_assoc name contract.requires_regions) then
        typed_error_at contract.loc
          "consumes_regions `%s` must also appear in requires_regions" name)
    contract.consumes_regions;
  let contract_for_call symbol =
    Option.bind
      (program.functions
      |> List.find_opt (fun callee ->
          callee.Typed_core.symbol.key = symbol.Typed_core.key))
      (fun callee ->
        callee.contracts
        |> List.find_opt (fun candidate -> candidate.Typed_core.mode = mode))
  in
  let rec infer_region env (expression : Typed_core.expr) =
    match expression.desc with
    | Var symbol -> List.assoc_opt symbol.key env
    | Apply (symbol, _) ->
        Option.bind (contract_for_call symbol) (fun contract ->
            Option.map
              (fun region ->
                {
                  region;
                  origin =
                    Printf.sprintf "call:%s:%d:%d" symbol.key
                      expression.loc.start.line expression.loc.start.column;
                })
              contract.result_region)
    | Let (symbol, value, body) ->
        let binding = infer_region env value in
        let env =
          match binding with
          | None -> env
          | Some binding -> (symbol.key, binding) :: env
        in
        infer_region env body
    | If (_, if_true, if_false) -> (
        match (infer_region env if_true, infer_region env if_false) with
        | Some left, Some right when left.region = right.region -> Some left
        | _ -> None)
    | Construct (constructor, arguments) -> (
        let candidates =
          region_definitions program mode
          |> List.filter_map (fun definition ->
              if
                typed_smt_sort definition.region_function.result
                <> typed_smt_sort expression.sort
              then None
              else
                let valid =
                  List.for_all2
                    (fun sort argument ->
                      if
                        typed_smt_sort sort
                        = typed_smt_sort definition.region_function.result
                      then
                        match infer_region env argument with
                        | Some binding ->
                            binding.region = definition.region_name
                        | None -> false
                      else true)
                    constructor.arguments arguments
                in
                if valid then Some definition.region_name else None)
          |> List.sort_uniq String.compare
        in
        match candidates with
        | [ region ] ->
            Some
              {
                region;
                origin =
                  Printf.sprintf "constructor-region:%d:%d"
                    expression.loc.start.line expression.loc.start.column;
              }
        | _ -> None)
    | _ -> None
  in
  let rec bind_pattern region env sort pattern =
    match pattern with
    | Typed_core.Pat_var symbol
      when typed_smt_sort sort
           = typed_smt_sort
               (find_region_definition program mode ~loc:contract.loc region)
                 .region_function
                 .result ->
        (symbol.key, { region; origin = "pattern:" ^ symbol.key }) :: env
    | Pat_alias (inner, symbol) ->
        bind_pattern region
          ((symbol.key, { region; origin = "pattern:" ^ symbol.key }) :: env)
          sort inner
    | Pat_tuple (tuple_sort, patterns) -> (
        match tuple_sort with
        | S_tuple sorts ->
            List.fold_left2 (bind_pattern region) env sorts patterns
        | _ -> env)
    | Pat_construct (constructor, patterns) ->
        List.fold_left2 (bind_pattern region) env constructor.arguments patterns
    | Pat_any | Pat_var _ | Pat_int _ | Pat_bool _ -> env
  in
  let rec proves_region env region (expression : Typed_core.expr) =
    match expression.desc with
    | Var symbol -> (
        match List.assoc_opt symbol.key env with
        | Some binding ->
            let _ = binding.origin in
            binding.region = region
        | None -> false)
    | Apply (symbol, _) -> (
        match contract_for_call symbol with
        | Some contract -> contract.Typed_core.result_region = Some region
        | None -> false)
    | Let (symbol, value, body) ->
        let env =
          if proves_region env region value then
            (symbol.key, { region; origin = "let-region:" ^ symbol.key }) :: env
          else
            match infer_region env value with
            | None -> env
            | Some binding -> (symbol.key, binding) :: env
        in
        proves_region env region body
    | If (_, if_true, if_false) ->
        proves_region env region if_true && proves_region env region if_false
    | Match (scrutinee, cases) ->
        let scrutinee_region = infer_region env scrutinee in
        List.for_all
          (fun (pattern, body) ->
            let env =
              match scrutinee_region with
              | None -> env
              | Some binding ->
                  bind_pattern binding.region env scrutinee.sort pattern
            in
            proves_region env region body)
          cases
    | Construct (constructor, arguments) ->
        let definition =
          find_region_definition program mode ~loc:expression.loc region
        in
        typed_smt_sort expression.sort
        = typed_smt_sort definition.region_function.result
        && List.for_all2
             (fun sort argument ->
               if
                 typed_smt_sort sort
                 = typed_smt_sort definition.region_function.result
               then proves_region env region argument
               else true)
             constructor.arguments arguments
    | _ -> false
  in
  Option.iter
    (fun region ->
      if not contract.result_recursive then
        typed_error_at contract.loc
          "result_region requires result_recursive = true";
      if not (proves_region initial_regions region function_def.body) then
        typed_error_at contract.loc
          "result_region `%s` is not preserved by recursive result fields"
          region)
    contract.result_region;
  let use_binding state loc binding =
    if List.mem binding.origin state.consumed_origins then
      typed_error_at loc "ownership region `%s` was used after consumption"
        binding.region;
    binding
  in
  let rec analyze state (expression : Typed_core.expr) =
    let analyze_list state expressions =
      List.fold_left
        (fun (bindings, state) expression ->
          let binding, state = analyze state expression in
          (binding :: bindings, state))
        ([], state) expressions
      |> fun (bindings, state) -> (List.rev bindings, state)
    in
    match expression.desc with
    | Var symbol ->
        let binding =
          Option.map
            (use_binding state expression.loc)
            (List.assoc_opt symbol.key state.region_env)
        in
        (binding, state)
    | Let (symbol, value, body) ->
        let binding, state = analyze state value in
        let state =
          match binding with
          | None -> state
          | Some binding ->
              let borrowed_origins =
                match value.desc with
                | Var _ -> binding.origin :: state.borrowed_origins
                | _ -> state.borrowed_origins
              in
              {
                state with
                region_env = (symbol.key, binding) :: state.region_env;
                borrowed_origins;
              }
        in
        analyze state body
    | Apply (symbol, arguments) ->
        let bindings, state = analyze_list state arguments in
        let callee =
          program.functions
          |> List.find_opt (fun callee ->
              callee.Typed_core.symbol.key = symbol.key)
        in
        let callee_contract =
          Option.bind callee (fun callee ->
              List.find_opt
                (fun candidate -> candidate.Typed_core.mode = mode)
                callee.contracts)
        in
        let state =
          match (callee, callee_contract) with
          | Some callee, Some callee_contract ->
              List.fold_left
                (fun state (formal_name, region) ->
                  let index =
                    List.find_mapi
                      (fun index ((formal : Typed_core.symbol), _) ->
                        if formal.display = formal_name then Some index
                        else None)
                      callee.arguments
                    |> Option.get
                  in
                  let binding =
                    match List.nth bindings index with
                    | Some binding when binding.region = region ->
                        use_binding state expression.loc binding
                    | None
                      when proves_region state.region_env region
                             (List.nth arguments index) ->
                        {
                          region;
                          origin =
                            Printf.sprintf "inline-region:%d:%d"
                              expression.loc.start.line
                              expression.loc.start.column;
                        }
                    | _ ->
                        typed_error_at expression.loc
                          "call `%s` needs ownership region `%s` for `%s`"
                          symbol.display region formal_name
                  in
                  if List.mem formal_name callee_contract.consumes_regions then (
                    if List.mem binding.origin state.borrowed_origins then
                      typed_error_at expression.loc
                        "borrowed ownership region `%s` cannot be consumed"
                        region;
                    if List.mem binding.origin state.consumed_origins then
                      typed_error_at expression.loc
                        "ownership region `%s` was consumed twice" region;
                    {
                      state with
                      consumed_origins =
                        binding.origin :: state.consumed_origins;
                    })
                  else state)
                state callee_contract.requires_regions
          | _ -> state
        in
        let binding =
          Option.bind callee_contract (fun contract ->
              Option.map
                (fun region ->
                  {
                    region;
                    origin =
                      Printf.sprintf "call:%s:%d:%d" symbol.key
                        expression.loc.start.line expression.loc.start.column;
                  })
                contract.result_region)
        in
        (binding, state)
    | Match (scrutinee, cases) ->
        let binding, state = analyze state scrutinee in
        let state =
          match binding with
          | None -> state
          | Some binding ->
              let binding = use_binding state expression.loc binding in
              {
                state with
                consumed_origins = binding.origin :: state.consumed_origins;
              }
        in
        let branch_results =
          List.map
            (fun (pattern, body) ->
              let branch_state =
                match binding with
                | None -> state
                | Some binding ->
                    {
                      state with
                      region_env =
                        bind_pattern binding.region state.region_env
                          scrutinee.sort pattern;
                    }
              in
              analyze branch_state body)
            cases
        in
        let binding =
          match branch_results with
          | (Some binding, _) :: rest
            when List.for_all
                   (function
                     | Some candidate, _ -> candidate.region = binding.region
                     | None, _ -> false)
                   rest ->
              Some binding
          | _ -> None
        in
        (binding, state)
    | If (condition, if_true, if_false) ->
        let _, state = analyze state condition in
        let true_binding, _ = analyze state if_true in
        let false_binding, _ = analyze state if_false in
        let binding =
          match (true_binding, false_binding) with
          | Some left, Some right when left.region = right.region -> Some left
          | _ -> None
        in
        (binding, state)
    | Construct (_, expressions)
    | Record (_, expressions)
    | Tuple expressions
    | Choose expressions ->
        let _, state = analyze_list state expressions in
        (infer_region state.region_env expression, state)
    | Ref (_, initial) ->
        let _, state = analyze state initial in
        (None, state)
    | Let_ref (_, _, initial, body) ->
        let _, state = analyze state initial in
        analyze state body
    | Sequence (first, second) ->
        let _, state = analyze state first in
        analyze state second
    | Assign (_, value) | Field (_, _, value) ->
        let _, state = analyze state value in
        (None, state)
    | Raise (_, payload) | Perform (_, payload) ->
        let state =
          Option.fold ~none:state
            ~some:(fun payload -> snd (analyze state payload))
            payload
        in
        (None, state)
    | Try (body, cases) ->
        let binding, state = analyze state body in
        List.iter (fun (_, handler) -> ignore (analyze state handler)) cases;
        (binding, state)
    | Handle (body, handlers) ->
        let binding, state = analyze state body in
        let rec action state = function
          | Typed_core.Abort expression | Resume expression ->
              ignore (analyze state expression)
          | Conditional (condition, if_true, if_false) ->
              ignore (analyze state condition);
              action state if_true;
              action state if_false
        in
        List.iter (fun (_, _, handler) -> action state handler) handlers;
        (binding, state)
    | Deref _ | Int _ | Bool _ -> (None, state)
  in
  ignore
    (analyze
       {
         region_env = initial_regions;
         consumed_origins = [];
         borrowed_origins = [];
       }
       function_def.body)

let region_frontier_specs program mode ~loc region ~root_sort ~root =
  let definition = find_region_definition program mode ~loc region in
  let paths =
    match
      returned_reference_paths ~recursive_frontier:true
        program.Typed_core.registry ~result_sort:root_sort ~result:root
    with
    | Ok paths -> paths
    | Error _ -> assert false
  in
  let expected = List.map (fun path -> path.path) paths in
  if
    List.sort String.compare expected
    <> List.sort String.compare
         (List.map fst definition.region_contract.result_references)
  then
    typed_error_at loc "ownership region `%s` has an incomplete frontier" region;
  List.map
    (fun path ->
      ( path,
        List.assoc path.path definition.region_contract.result_references,
        definition.region_contract.loc ))
    paths
