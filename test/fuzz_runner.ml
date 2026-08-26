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
  let int_sort = Base Refined_ir.Typed_core.S_int in
  let predicate_sort = Arrow (int_sort, Base S_bool) in
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
        | Horn_not_supported generic -> "unexpected horn " ^ generic
        | Arity_mismatch -> "arity"
        | Unsolved_hindley generic -> "unsolved " ^ generic
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

let () =
  let cases = env_int "REFINED_FUZZ_CASES" 5_000 in
  let seed = env_int "REFINED_FUZZ_SEED" 0x5eed_2026 in
  if cases <= 0 then failwith "REFINED_FUZZ_CASES must be positive";
  let random = Random.State.make [| seed |] in
  try
    for case = 0 to cases - 1 do
      fuzz_evars random case;
      fuzz_hindley random case
    done;
    Printf.printf "fuzz: %d cases passed (seed=%d)\n%!" cases seed
  with Fuzz_failure (case, message) ->
    Printf.eprintf "fuzz failure: seed=%d case=%d: %s\n%!" seed case message;
    exit 1
