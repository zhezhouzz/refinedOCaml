exception Fuzz_failure of int * string

let env_int name default =
  match Sys.getenv_opt name with
  | None -> default
  | Some value -> (
      match int_of_string_opt value with
      | Some value -> value
      | None -> failwith (name ^ " must be an integer"))

let fail case message = raise (Fuzz_failure (case, message))

module Fuzz_term = struct
  type head = Atom of int | Branch of int
  type t = Variable of string | Node of head * t list

  let view = function
    | Variable variable -> `Variable variable
    | Node (head, children) -> `Node (head, children)

  let make_node head children = Node (head, children)
  let equal_head = ( = )
  let equal = ( = )
end

module Fuzz_evars = Refined_ir.Evar_context.Make (Fuzz_term)

module Horn_term = struct
  type parameter = string

  type t =
    | False
    | True
    | Reference of string
    | Or of t list
    | Lambda of string * t

  let falsity = False

  let rec normalize = function
    | Or terms -> (
        let terms =
          terms |> List.map normalize
          |> List.concat_map (function Or nested -> nested | term -> [ term ])
          |> List.filter (( <> ) False)
          |> List.sort_uniq compare
        in
        if List.mem True terms then True
        else
          match terms with [] -> False | [ term ] -> term | terms -> Or terms)
    | Lambda (parameter, body) -> Lambda (parameter, normalize body)
    | (False | True | Reference _) as term -> term

  let join terms = normalize (Or terms)
  let lambda ~parameter body = Lambda (parameter, normalize body)

  let rec instantiate solutions = function
    | Reference name -> (
        match List.assoc_opt name solutions with
        | Some (Lambda (_, body)) -> body
        | Some body -> body
        | None -> Reference name)
    | Or terms -> Or (List.map (instantiate solutions) terms) |> normalize
    | Lambda (parameter, body) -> Lambda (parameter, instantiate solutions body)
    | (False | True) as term -> term

  let abstract ~argument:_ ~parameter:_ body = body

  let rec dependencies ~variables = function
    | Reference name when List.mem name variables -> [ name ]
    | Or terms -> List.concat_map (dependencies ~variables) terms
    | Lambda (_, body) -> dependencies ~variables body
    | False | True | Reference _ -> []

  let equal left right = normalize left = normalize right
end

module Horn_solver = Refined_ir.Horn_fixpoint.Make (Horn_term)

let rec ground_term random depth =
  if depth = 0 || Random.State.int random 4 = 0 then
    Fuzz_term.Node (Atom (Random.State.int random 32), [])
  else
    let arity = 1 + Random.State.int random 3 in
    Fuzz_term.Node
      (Branch arity, List.init arity (fun _ -> ground_term random (depth - 1)))

let abstract_term random ground =
  let counter = ref 0 in
  let variables = ref [] in
  let fresh () =
    let variable = "e" ^ string_of_int !counter in
    incr counter;
    variables := variable :: !variables;
    Fuzz_term.Variable variable
  in
  let rec abstract depth = function
    | Fuzz_term.Node (_, _) when depth > 0 && Random.State.int random 4 = 0 ->
        fresh ()
    | Node (head, children) ->
        Node (head, List.map (abstract (depth + 1)) children)
    | Variable _ -> assert false
  in
  let template = abstract 1 ground in
  (template, !variables)

let fuzz_evars random case =
  let ground = ground_term random (1 + Random.State.int random 5) in
  let template, variables = abstract_term random ground in
  let context = Fuzz_evars.create () in
  (match Fuzz_evars.unify context ~formal:template ~actual:ground with
  | Error _ -> fail case "generated solvable evar template did not unify"
  | Ok () -> ());
  if Fuzz_evars.substitute context template <> ground then
    fail case "evar substitution did not reconstruct the ground term";
  if not (Fuzz_evars.is_complete context ~variables) then
    fail case "evar context remained incomplete after successful unification";
  let cyclic = Fuzz_evars.create () in
  let variable = "cycle" ^ string_of_int case in
  let recursive = Fuzz_term.Node (Branch 1, [ Fuzz_term.Variable variable ]) in
  match
    Fuzz_evars.unify cyclic ~formal:(Fuzz_term.Variable variable)
      ~actual:recursive
  with
  | Error (Occurs _) -> ()
  | Ok () | Error (Shape_mismatch _) ->
      fail case "occurs-check accepted a recursive evar solution"

let rec random_boolean_term random variable depth =
  let open Refined_ir.Generic_refinement in
  let integer () = Integer (Random.State.int random 201 - 100) in
  if depth = 0 then
    if Random.State.bool random then Greater (Variable variable, integer ())
    else Equal (Add (Variable variable, integer ()), integer ())
  else
    match Random.State.int random 4 with
    | 0 -> Not (random_boolean_term random variable (depth - 1))
    | 1 ->
        And
          [
            random_boolean_term random variable (depth - 1);
            random_boolean_term random variable (depth - 1);
          ]
    | 2 ->
        Or
          [
            random_boolean_term random variable (depth - 1);
            random_boolean_term random variable (depth - 1);
          ]
    | _ -> random_boolean_term random variable 0

let fuzz_hindley random case =
  let open Refined_ir.Generic_refinement in
  let int_sort = Base Int in
  let predicate_sort = Arrow (int_sort, Base Bool) in
  let indexed index =
    Refined
      {
        base = "Predicate";
        index_sort = predicate_sort;
        index;
        predicate = Boolean true;
      }
  in
  let input_body =
    random_boolean_term random "arg" (Random.State.int random 4)
  in
  let input = Lambda ("arg", int_sort, input_body) in
  let output_index, expected_index =
    let applied = normalize (Apply (input, Variable "out")) in
    match Random.State.int random 4 with
    | 0 -> (Generic "property", input)
    | 1 ->
        ( Lambda
            ("out", int_sort, Not (Apply (Generic "property", Variable "out"))),
          Lambda ("out", int_sort, Not applied) )
    | 2 ->
        let extra = random_boolean_term random "out" 1 in
        ( Lambda
            ( "out",
              int_sort,
              And [ Apply (Generic "property", Variable "out"); extra ] ),
          Lambda ("out", int_sort, And [ applied; extra ]) )
    | _ ->
        let extra = random_boolean_term random "out" 1 in
        ( Lambda
            ( "out",
              int_sort,
              Or [ Apply (Generic "property", Variable "out"); extra ] ),
          Lambda ("out", int_sort, Or [ applied; extra ]) )
  in
  let scheme =
    Forall
      ( { name = "property"; mode = Hindley; sort = predicate_sort },
        Mono (Function (indexed (Generic "property"), indexed output_index)) )
  in
  match elaborate_application scheme [ indexed input ] with
  | Error error ->
      fail case
        ("generated Hindley application failed: "
        ^
        match error with
        | Ill_sorted message | Type_mismatch message -> message
        | Ill_formed_hindley generic -> "ill-formed " ^ generic
        | Ill_formed_horn generic -> "ill-formed horn " ^ generic
        | Arity_mismatch -> "arity"
        | Unsolved_hindley generic -> "unsolved " ^ generic
        | Unsolved_horn generic -> "unsolved horn " ^ generic
        | Unsupported_horn_constraint generic -> "unsupported horn " ^ generic
        | Horn_fixpoint_did_not_converge iterations ->
            "horn divergence " ^ string_of_int iterations
        | Cyclic_instantiation evar -> "cyclic " ^ evar)
  | Ok elaboration ->
      if
        elaboration.instantiations
        <> [ { generic = "property"; refinement = input } ]
      then fail case "wrong ghost instantiation";
      if elaboration.result <> indexed expected_index then
        fail case "substitution or beta-reduction produced the wrong result";
      if List.length elaboration.constraints <> 1 then
        fail case "application did not emit exactly one argument constraint"

let fuzz_horn random case =
  let open Refined_ir.Generic_refinement in
  let int_sort = Base Int in
  let predicate_sort = Arrow (int_sort, Base Bool) in
  let index = Random.State.int random 200 - 100 in
  let threshold =
    let candidate = Random.State.int random 200 - 100 in
    if candidate = index then candidate + 1 else candidate
  in
  let refined predicate =
    Refined
      { base = "int"; index_sort = int_sort; index = Integer index; predicate }
  in
  let application = Apply (Generic "property", Integer index) in
  let scheme =
    Forall
      ( { name = "property"; mode = Horn; sort = predicate_sort },
        Mono (Function (refined application, refined application)) )
  in
  let assumption = Greater (Integer index, Integer threshold) in
  (match elaborate_application scheme [ refined assumption ] with
  | Error _ -> fail case "generated positive Horn constraint was not solved"
  | Ok elaboration ->
      let expected =
        Lambda
          ( "horn_property",
            int_sort,
            Greater (Variable "horn_property", Integer threshold) )
      in
      if
        not
          (List.exists
             (fun instantiation ->
               instantiation.generic = "property"
               && instantiation.refinement = expected)
             elaboration.instantiations)
      then fail case "Horn solver inferred the wrong lower-bound predicate");
  let invalid =
    Forall
      ( { name = "property"; mode = Horn; sort = predicate_sort },
        Mono
          (Function
             (refined (Or [ application; Boolean true ]), refined application))
      )
  in
  match well_formed invalid with
  | Error (Ill_formed_horn "property") -> ()
  | Ok () | Error _ -> fail case "Horn positivity check accepted disjunction"

let fuzz_recursive_horn random case =
  let count = 1 + Random.State.int random 6 in
  let names = List.init count (fun index -> "P" ^ string_of_int index) in
  let variables =
    List.map (fun name -> Horn_solver.{ name; parameter = "arg_" ^ name }) names
  in
  let base = Array.init count (fun _ -> Random.State.int random 4 = 0) in
  let edges = ref [] in
  let clauses = ref [] in
  List.iteri
    (fun head name ->
      if base.(head) then
        clauses :=
          Horn_solver.{ head = name; argument = Horn_term.True; body = True }
          :: !clauses;
      let edge_count = Random.State.int random (count + 1) in
      for _ = 1 to edge_count do
        let dependency = Random.State.int random count in
        edges := (head, dependency) :: !edges;
        clauses :=
          Horn_solver.
            {
              head = name;
              argument = Horn_term.True;
              body = Reference (List.nth names dependency);
            }
          :: !clauses
      done)
    names;
  let expected = Array.copy base in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun (head, dependency) ->
        if expected.(dependency) && not expected.(head) then (
          expected.(head) <- true;
          changed := true))
      !edges
  done;
  match Horn_solver.solve ~variables ~clauses:!clauses () with
  | Error _ -> fail case "finite recursive Horn graph did not converge"
  | Ok solution ->
      List.iteri
        (fun index name ->
          let expected_body =
            if expected.(index) then Horn_term.True else False
          in
          match List.assoc_opt name solution.predicates with
          | Some (Lambda (_, body)) when body = expected_body -> ()
          | _ -> fail case "Horn fixpoint disagreed with graph reachability")
        names

let fuzz_function_scc random case =
  let open Refined_ir.Typed_core in
  let count = 1 + Random.State.int random 7 in
  let symbols =
    Array.init count (fun index ->
        let name = "f" ^ string_of_int index in
        { key = name; display = name })
  in
  let edges = Array.make_matrix count count false in
  for caller = 0 to count - 1 do
    for callee = 0 to count - 1 do
      edges.(caller).(callee) <- Random.State.int random 5 = 0
    done
  done;
  let position = Refined_ir.Source_span.{ offset = 0; line = 1; column = 0 } in
  let loc =
    Refined_ir.Source_span.
      { file = "<function-scc-fuzz>"; start = position; finish = position }
  in
  let call callee =
    {
      desc = Apply (symbols.(callee), []);
      sort = S_int;
      refinement = None;
      loc;
    }
  in
  let functions =
    Array.to_list
      (Array.mapi
         (fun caller symbol ->
           let calls =
             List.init count Fun.id
             |> List.filter_map (fun callee ->
                 if edges.(caller).(callee) then Some (call callee) else None)
           in
           let body =
             match calls with
             | [] -> { desc = Int 0; sort = S_int; refinement = None; loc }
             | [ call ] -> call
             | calls ->
                 {
                   desc = Tuple calls;
                   sort = S_tuple (List.map (fun _ -> S_int) calls);
                   refinement = None;
                   loc;
                 }
           in
           {
             symbol;
             arguments = [];
             result = body.sort;
             body;
             contracts = [];
             measure = None;
           })
         symbols)
  in
  let registry =
    {
      constructors_by_uid = Hashtbl.create 0;
      constructors_by_name = Hashtbl.create 0;
      fields_by_uid = Hashtbl.create 0;
      fields_by_name = Hashtbl.create 0;
      logic_by_name = Hashtbl.create 0;
      abstract_sorts_by_name = Hashtbl.create 0;
      concrete_sorts_by_name = Hashtbl.create 0;
      choose_symbols = Hashtbl.create 0;
      module_aliases = Hashtbl.create 0;
      functor_theories = Hashtbl.create 0;
      generic_schemes_by_name = Hashtbl.create 0;
      axioms = [];
      lemmas = [];
      checked_lemmas = [];
      proof_artifacts = [];
      datatype_templates = [];
      datatypes = [];
    }
  in
  let analysis = Refined_ir.Function_analysis.analyze { registry; functions } in
  let reachable = Array.map Array.copy edges in
  for intermediate = 0 to count - 1 do
    for caller = 0 to count - 1 do
      for callee = 0 to count - 1 do
        reachable.(caller).(callee) <-
          reachable.(caller).(callee)
          || reachable.(caller).(intermediate)
             && reachable.(intermediate).(callee)
      done
    done
  done;
  for caller = 0 to count - 1 do
    let expected_dependencies =
      List.init count Fun.id
      |> List.filter (fun callee -> edges.(caller).(callee))
      |> List.map (fun callee -> symbols.(callee).key)
    in
    if
      List.assoc symbols.(caller).key analysis.dependency_graph
      <> expected_dependencies
    then fail case "function call graph lost or invented an edge";
    if
      Refined_ir.Function_analysis.is_recursive_function analysis
        symbols.(caller).key
      <> reachable.(caller).(caller)
    then fail case "function SCC recursion disagreed with transitive closure";
    for callee = 0 to count - 1 do
      if edges.(caller).(callee) then
        let expected =
          reachable.(caller).(callee) && reachable.(callee).(caller)
        in
        if
          Refined_ir.Function_analysis.is_recursive_edge analysis
            ~caller:symbols.(caller).key ~callee:symbols.(callee).key
          <> expected
        then fail case "recursive call edge disagreed with SCC oracle"
    done
  done

let fuzz_theory_slice random case =
  let statement_count = 1 + Random.State.int random 8 in
  let symbol_count = 1 + Random.State.int random 8 in
  let names =
    Array.init statement_count (fun index -> "A" ^ string_of_int index)
  in
  let symbols =
    Array.init symbol_count (fun index -> "S" ^ string_of_int index)
  in
  let statement_symbols =
    Array.make_matrix statement_count symbol_count false
  in
  let requirements = Array.make_matrix statement_count statement_count false in
  let statements =
    List.init statement_count (fun statement ->
        let used_symbols =
          List.init symbol_count Fun.id
          |> List.filter_map (fun symbol ->
              let used = Random.State.int random 4 = 0 in
              statement_symbols.(statement).(symbol) <- used;
              if used then Some symbols.(symbol) else None)
        in
        let requires =
          List.init statement_count Fun.id
          |> List.filter_map (fun dependency ->
              let required = Random.State.int random 8 = 0 in
              requirements.(statement).(dependency) <- required;
              if required then Some names.(dependency) else None)
        in
        Refined_ir.Theory_slice.
          { name = names.(statement); symbols = used_symbols; requires })
  in
  let active_symbols =
    Array.init symbol_count (fun _ -> Random.State.int random 4 = 0)
  in
  let roots =
    List.init symbol_count Fun.id
    |> List.filter_map (fun symbol ->
        if active_symbols.(symbol) then Some symbols.(symbol) else None)
  in
  let selected = Array.make statement_count false in
  let required_names = Array.make statement_count false in
  let changed = ref true in
  while !changed do
    changed := false;
    for statement = 0 to statement_count - 1 do
      let touches_active =
        let found = ref false in
        for symbol = 0 to symbol_count - 1 do
          found :=
            !found
            || statement_symbols.(statement).(symbol)
               && active_symbols.(symbol)
        done;
        !found
      in
      if
        (required_names.(statement) || touches_active)
        && not selected.(statement)
      then (
        selected.(statement) <- true;
        changed := true;
        for symbol = 0 to symbol_count - 1 do
          if statement_symbols.(statement).(symbol) then
            active_symbols.(symbol) <- true
        done;
        for dependency = 0 to statement_count - 1 do
          if requirements.(statement).(dependency) then
            required_names.(dependency) <- true
        done)
    done
  done;
  let expected_names =
    List.init statement_count Fun.id
    |> List.filter_map (fun statement ->
        if selected.(statement) then Some names.(statement) else None)
  in
  let expected_symbols =
    List.init symbol_count Fun.id
    |> List.filter_map (fun symbol ->
        if active_symbols.(symbol) then Some symbols.(symbol) else None)
  in
  let actual = Refined_ir.Theory_slice.close ~roots statements in
  if actual.statement_names <> expected_names then
    fail case "theory slice statement closure disagreed with graph oracle";
  if actual.symbols <> expected_symbols then
    fail case "theory slice symbol closure disagreed with graph oracle"

let fuzz_relational_outcomes random case =
  let module R = Refined_ir.Relational_outcome in
  let state = [ ("cell", "v0") ] in
  let count = 1 + Random.State.int random 8 in
  let return_count = ref 0 in
  let performed_count = ref 0 in
  let relation =
    List.init count (fun index ->
        match Random.State.int random 3 with
        | 0 ->
            incr return_count;
            R.return ~state ("v" ^ string_of_int index)
        | 1 -> R.raise_ ~state ("E" ^ string_of_int index)
        | _ ->
            incr performed_count;
            R.perform ~state ~operation:"Op"
              ~payload:("p" ^ string_of_int index)
              ~continuation:("k" ^ string_of_int index)
              ())
    |> List.concat
  in
  let continued = ref 0 in
  let bound =
    R.bind relation (fun value state ->
        incr continued;
        R.return ~state value)
  in
  if !continued <> !return_count || List.length bound <> List.length relation
  then fail case "relational bind violated abnormal-outcome propagation";
  let caught =
    R.try_with bound (fun ~exception_ ~payload:_ ~state ->
        R.return ~state exception_)
  in
  if
    List.exists
      (fun path -> match path.R.outcome with Raised _ -> true | _ -> false)
      caught
  then fail case "exception handler left a raised path";
  let handled_continuations = ref 0 in
  let handled =
    R.handle_effect ~operation:"Op" caught (fun ~payload ~continuation ~state ->
        if Option.is_some continuation then incr handled_continuations;
        R.return ~state (Option.get payload))
  in
  if !handled_continuations <> !performed_count then
    fail case "effect handler lost continuation identities";
  if
    List.exists
      (fun path ->
        match path.R.outcome with
        | Performed { operation = "Op"; _ } -> true
        | _ -> false)
      handled
  then fail case "effect handler left a matching performed path";
  match
    R.bind (R.write ~state ~cell:"cell" ~value:"v1") (fun _ state ->
        R.read ~state ~cell:"cell")
  with
  | [ { outcome = Return "v1"; _ } ] -> ()
  | _ -> fail case "relational state write/read lost its value"

let () =
  let cases = env_int "REFINED_FUZZ_CASES" 5_000 in
  let seed = env_int "REFINED_FUZZ_SEED" 0x5eed_2026 in
  if cases <= 0 then failwith "REFINED_FUZZ_CASES must be positive";
  let property case_seed =
    let random = Random.State.make [| case_seed |] in
    try
      fuzz_evars random case_seed;
      fuzz_hindley random case_seed;
      fuzz_horn random case_seed;
      fuzz_recursive_horn random case_seed;
      fuzz_function_scc random case_seed;
      fuzz_theory_slice random case_seed;
      fuzz_relational_outcomes random case_seed;
      true
    with Fuzz_failure (_case, message) ->
      QCheck2.Test.fail_reportf "seed=%d: %s" case_seed message
  in
  let test =
    QCheck2.Test.make ~count:cases ~name:"refinedOCaml semantic oracles"
      ~print:string_of_int QCheck2.Gen.int property
  in
  let random = Random.State.make [| seed |] in
  (try QCheck2.Test.check_exn ~rand:random test
   with exception_ ->
     Printf.eprintf "fuzz failure: master-seed=%d\n%!" seed;
     raise exception_);
  Printf.printf "fuzz: %d cases passed (seed=%d, qcheck2-shrinking)\n%!" cases
    seed
