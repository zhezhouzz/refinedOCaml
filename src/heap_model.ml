open Refined_ir
open Refined_common
open Vc_logic

type state = (string * string) list

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
