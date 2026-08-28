type state = (string * string) list

type outcome =
  | Return of string
  | Raised of string
  | Performed of { operation : string; payload : string }

type path = {
  guard : string;
  initial_state : state;
  final_state : state;
  outcome : outcome;
}

type t = path list

let app name arguments = "(" ^ String.concat " " (name :: arguments) ^ ")"

let conjunction = function
  | [] -> "true"
  | [ predicate ] -> predicate
  | predicates -> app "and" predicates

let disjunction = function
  | [] -> "false"
  | [ predicate ] -> predicate
  | predicates -> app "or" predicates

let return ~state value =
  [
    {
      guard = "true";
      initial_state = state;
      final_state = state;
      outcome = Return value;
    };
  ]

let raise_ ~state exception_ =
  [
    {
      guard = "true";
      initial_state = state;
      final_state = state;
      outcome = Raised exception_;
    };
  ]

let perform ~state ~operation ~payload =
  [
    {
      guard = "true";
      initial_state = state;
      final_state = state;
      outcome = Performed { operation; payload };
    };
  ]

let read ~state ~cell =
  match List.assoc_opt cell state with
  | Some value -> return ~state value
  | None -> invalid_arg ("unknown relational cell " ^ cell)

let set state cell value = (cell, value) :: List.remove_assoc cell state

let write ~state ~cell ~value =
  if not (List.mem_assoc cell state) then
    invalid_arg ("unknown relational cell " ^ cell);
  [
    {
      guard = "true";
      initial_state = state;
      final_state = set state cell value;
      outcome = Return "unit";
    };
  ]

let guarded condition path =
  { path with guard = conjunction [ condition; path.guard ] }

let branch ~condition ~if_true ~if_false =
  List.map (guarded condition) if_true
  @ List.map (guarded (app "not" [ condition ])) if_false

let compose parent child =
  {
    child with
    guard = conjunction [ parent.guard; child.guard ];
    initial_state = parent.initial_state;
  }

let bind relation continuation =
  List.concat_map
    (fun path ->
      match path.outcome with
      | Return value ->
          continuation value path.final_state |> List.map (compose path)
      | Raised _ | Performed _ -> [ path ])
    relation

let try_with relation handler =
  List.concat_map
    (fun path ->
      match path.outcome with
      | Raised exception_ ->
          handler exception_ path.final_state |> List.map (compose path)
      | Return _ | Performed _ -> [ path ])
    relation

let handle_effect ~operation relation handler =
  List.concat_map
    (fun path ->
      match path.outcome with
      | Performed performed when performed.operation = operation ->
          handler ~payload:performed.payload ~state:path.final_state
          |> List.map (compose path)
      | Return _ | Raised _ | Performed _ -> [ path ])
    relation

let safety_obligation ~pre ~normal ~raised ~performed relation =
  relation
  |> List.map (fun path ->
      let post =
        match path.outcome with
        | Return value ->
            normal ~value ~initial:path.initial_state ~final:path.final_state
        | Raised exception_ ->
            raised ~exception_ ~initial:path.initial_state
              ~final:path.final_state
        | Performed { operation; payload } ->
            performed ~operation ~payload ~initial:path.initial_state
              ~final:path.final_state
      in
      app "=>" [ conjunction [ pre; path.guard ]; post ])
  |> conjunction

let coverage_obligation ~target ~matches relation =
  let reachable =
    relation
    |> List.map (fun path -> conjunction [ path.guard; matches path ])
    |> disjunction
  in
  app "=>" [ target; reachable ]
