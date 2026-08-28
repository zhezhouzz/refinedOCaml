module type TERM = sig
  type t
  type parameter

  val falsity : t
  val join : t list -> t
  val lambda : parameter:parameter -> t -> t
  val instantiate : (string * t) list -> t -> t
  val abstract : argument:t -> parameter:parameter -> t -> t
  val dependencies : variables:string list -> t -> string list
  val equal : t -> t -> bool
end

module Make (Term : TERM) = struct
  type variable = { name : string; parameter : Term.parameter }
  type clause = { head : string; argument : Term.t; body : Term.t }

  type solution = {
    predicates : (string * Term.t) list;
    dependency_graph : (string * string list) list;
    strongly_connected_components : string list list;
    iterations : int;
  }

  type error = Did_not_converge of int

  let unique strings = List.sort_uniq String.compare strings

  let dependency_graph variables clauses =
    let names = List.map (fun variable -> variable.name) variables in
    List.map
      (fun variable ->
        let dependencies =
          clauses
          |> List.filter (fun clause -> clause.head = variable.name)
          |> List.concat_map (fun clause ->
              Term.dependencies ~variables:names clause.body)
          |> unique
        in
        (variable.name, dependencies))
      variables

  let strongly_connected_components graph =
    let index = ref 0 in
    let indices = Hashtbl.create 16 in
    let lowlinks = Hashtbl.create 16 in
    let on_stack = Hashtbl.create 16 in
    let stack = Stack.create () in
    let components = ref [] in
    let neighbours node =
      Option.value (List.assoc_opt node graph) ~default:[]
    in
    let rec visit node =
      let node_index = !index in
      incr index;
      Hashtbl.add indices node node_index;
      Hashtbl.add lowlinks node node_index;
      Stack.push node stack;
      Hashtbl.replace on_stack node true;
      List.iter
        (fun neighbour ->
          if not (Hashtbl.mem indices neighbour) then (
            visit neighbour;
            Hashtbl.replace lowlinks node
              (min
                 (Hashtbl.find lowlinks node)
                 (Hashtbl.find lowlinks neighbour)))
          else if
            Option.value (Hashtbl.find_opt on_stack neighbour) ~default:false
          then
            Hashtbl.replace lowlinks node
              (min
                 (Hashtbl.find lowlinks node)
                 (Hashtbl.find indices neighbour)))
        (neighbours node);
      if Hashtbl.find lowlinks node = Hashtbl.find indices node then (
        let component = ref [] in
        let finished = ref false in
        while not !finished do
          let member = Stack.pop stack in
          Hashtbl.replace on_stack member false;
          component := member :: !component;
          finished := member = node
        done;
        components := List.sort String.compare !component :: !components)
    in
    List.iter
      (fun (node, _) -> if not (Hashtbl.mem indices node) then visit node)
      graph;
    List.rev !components

  let solve ?(max_iterations = 64) ~variables ~clauses () =
    let graph = dependency_graph variables clauses in
    let components = strongly_connected_components graph in
    let initial =
      List.map
        (fun variable ->
          (variable.name, Term.lambda ~parameter:variable.parameter Term.falsity))
        variables
    in
    let next predicates =
      List.map
        (fun variable ->
          let bodies =
            clauses
            |> List.filter (fun clause -> clause.head = variable.name)
            |> List.map (fun clause ->
                clause.body
                |> Term.instantiate predicates
                |> Term.abstract ~argument:clause.argument
                     ~parameter:variable.parameter)
          in
          ( variable.name,
            Term.lambda ~parameter:variable.parameter (Term.join bodies) ))
        variables
    in
    let equal_solutions left right =
      List.for_all2
        (fun (left_name, left) (right_name, right) ->
          left_name = right_name && Term.equal left right)
        left right
    in
    let rec iterate iteration predicates =
      if iteration > max_iterations then Error (Did_not_converge max_iterations)
      else
        let updated = next predicates in
        if equal_solutions predicates updated then
          Ok
            {
              predicates = updated;
              dependency_graph = graph;
              strongly_connected_components = components;
              iterations = iteration;
            }
        else iterate (iteration + 1) updated
    in
    if max_iterations <= 0 then Error (Did_not_converge max_iterations)
    else iterate 1 initial
end
