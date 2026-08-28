type t = {
  dependency_graph : (string * string list) list;
  strongly_connected_components : string list list;
}

let calls expression =
  let rec collect accumulator (expression : Typed_core.expr) =
    let collect_all expressions =
      List.fold_left collect accumulator expressions
    in
    match expression.desc with
    | Var _ | Int _ | Bool _ -> accumulator
    | Tuple expressions
    | Choose expressions
    | Construct (_, expressions)
    | Record (_, expressions) ->
        collect_all expressions
    | Apply (symbol, arguments) ->
        List.fold_left collect (symbol.key :: accumulator) arguments
    | If (condition, if_true, if_false) ->
        List.fold_left collect accumulator [ condition; if_true; if_false ]
    | Let (_, value, body) -> List.fold_left collect accumulator [ value; body ]
    | Match (scrutinee, cases) ->
        List.fold_left
          (fun accumulator (_, body) -> collect accumulator body)
          (collect accumulator scrutinee)
          cases
    | Field (_, _, record) -> collect accumulator record
  in
  collect [] expression |> List.sort_uniq String.compare

let strongly_connected_components graph =
  let index = ref 0 in
  let indices = Hashtbl.create (List.length graph) in
  let lowlinks = Hashtbl.create (List.length graph) in
  let on_stack = Hashtbl.create (List.length graph) in
  let stack = Stack.create () in
  let components = ref [] in
  let rec visit vertex =
    let vertex_index = !index in
    incr index;
    Hashtbl.add indices vertex vertex_index;
    Hashtbl.add lowlinks vertex vertex_index;
    Stack.push vertex stack;
    Hashtbl.replace on_stack vertex true;
    let successors = Option.value (List.assoc_opt vertex graph) ~default:[] in
    List.iter
      (fun successor ->
        if not (Hashtbl.mem indices successor) then (
          visit successor;
          Hashtbl.replace lowlinks vertex
            (min
               (Hashtbl.find lowlinks vertex)
               (Hashtbl.find lowlinks successor)))
        else if
          Option.value (Hashtbl.find_opt on_stack successor) ~default:false
        then
          Hashtbl.replace lowlinks vertex
            (min
               (Hashtbl.find lowlinks vertex)
               (Hashtbl.find indices successor)))
      successors;
    if Hashtbl.find lowlinks vertex = Hashtbl.find indices vertex then (
      let component = ref [] in
      let finished = ref false in
      while not !finished do
        let member = Stack.pop stack in
        Hashtbl.replace on_stack member false;
        component := member :: !component;
        finished := String.equal member vertex
      done;
      components := List.sort String.compare !component :: !components)
  in
  List.iter
    (fun (vertex, _) -> if not (Hashtbl.mem indices vertex) then visit vertex)
    graph;
  List.rev !components

let analyze (program : Typed_core.program) =
  let functions =
    List.map
      (fun (function_def : Typed_core.function_def) -> function_def.symbol.key)
      program.functions
  in
  let is_function key = List.mem key functions in
  let dependency_graph =
    List.map
      (fun (function_def : Typed_core.function_def) ->
        ( function_def.symbol.key,
          calls function_def.body |> List.filter is_function ))
      program.functions
  in
  {
    dependency_graph;
    strongly_connected_components =
      strongly_connected_components dependency_graph;
  }

let component_of analysis function_ =
  List.find_opt
    (List.exists (String.equal function_))
    analysis.strongly_connected_components

let is_recursive_edge analysis ~caller ~callee =
  let dependencies =
    Option.value (List.assoc_opt caller analysis.dependency_graph) ~default:[]
  in
  match component_of analysis caller with
  | Some component ->
      List.mem callee dependencies
      && List.mem callee component
      && (List.length component > 1 || List.mem caller dependencies)
  | None -> false

let is_recursive_function analysis function_ =
  match component_of analysis function_ with
  | None -> false
  | Some component ->
      List.length component > 1
      || List.mem function_
           (Option.value
              (List.assoc_opt function_ analysis.dependency_graph)
              ~default:[])
