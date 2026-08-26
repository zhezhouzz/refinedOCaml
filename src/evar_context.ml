module type TERM = sig
  type t
  type head

  val view : t -> [ `Variable of string | `Node of head * t list ]
  val make_node : head -> t list -> t
  val equal_head : head -> head -> bool
  val equal : t -> t -> bool
end

module Make (Term : TERM) = struct
  type context = (string, Term.t) Hashtbl.t
  type error = Occurs of string * Term.t | Shape_mismatch of Term.t * Term.t

  let create () = Hashtbl.create 8
  let solution context variable = Hashtbl.find_opt context variable
  let has_solutions context = Hashtbl.length context > 0

  let rec occurs variable term =
    match Term.view term with
    | `Variable candidate -> candidate = variable
    | `Node (_, children) -> List.exists (occurs variable) children

  let rec substitute context term =
    match Term.view term with
    | `Variable variable -> (
        match solution context variable with
        | None -> term
        | Some solution -> substitute context solution)
    | `Node (head, children) ->
        Term.make_node head (List.map (substitute context) children)

  let rec unify context ~formal ~actual =
    let formal = substitute context formal in
    let actual = substitute context actual in
    if Term.equal formal actual then Ok ()
    else
      match (Term.view formal, Term.view actual) with
      | `Variable variable, _ ->
          if occurs variable actual then Error (Occurs (variable, actual))
          else (
            Hashtbl.replace context variable actual;
            Ok ())
      | ( `Node (formal_head, formal_children),
          `Node (actual_head, actual_children) )
        when Term.equal_head formal_head actual_head
             && List.length formal_children = List.length actual_children ->
          List.fold_left2
            (fun result formal actual ->
              Result.bind result (fun () -> unify context ~formal ~actual))
            (Ok ()) formal_children actual_children
      | _ -> Error (Shape_mismatch (formal, actual))

  let is_complete context ~variables =
    List.for_all
      (fun variable -> Option.is_some (solution context variable))
      variables
end
