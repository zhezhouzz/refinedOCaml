type base_sort = Int | Bool | Unit | Named of string
type sort = Base of base_sort | Arrow of sort * sort

type term =
  | Integer of int
  | Boolean of bool
  | Variable of string
  | Generic of string
  | Evar of string
  | Lambda of string * sort * term
  | Apply of term * term
  | Not of term
  | And of term list
  | Or of term list
  | Equal of term * term
  | Add of term * term
  | Greater of term * term

type generic_mode = Hindley | Horn
type generic = { name : string; mode : generic_mode; sort : sort }

type type_ =
  | Refined of {
      base : string;
      index_sort : sort;
      index : term;
      predicate : term;
    }
  | Function of type_ * type_

type scheme = Mono of type_ | Forall of generic * scheme
type constraint_ = { assumption : term; requirement : term }
type instantiation = { generic : string; refinement : term }

type elaboration = {
  instantiations : instantiation list;
  result : type_;
  constraints : constraint_ list;
}

type error =
  | Ill_sorted of string
  | Ill_formed_hindley of string
  | Horn_not_supported of string
  | Type_mismatch of string
  | Arity_mismatch
  | Unsolved_hindley of string
  | Cyclic_instantiation of string

let string_of_base_sort = function
  | Int -> "int"
  | Bool -> "bool"
  | Unit -> "unit"
  | Named name -> name

let rec string_of_sort = function
  | Base sort -> string_of_base_sort sort
  | Arrow (input, output) ->
      "(" ^ string_of_sort input ^ " -> " ^ string_of_sort output ^ ")"

let rec string_of_term = function
  | Integer integer -> string_of_int integer
  | Boolean boolean -> string_of_bool boolean
  | Variable variable | Generic variable | Evar variable -> variable
  | Lambda (parameter, sort, body) ->
      Printf.sprintf "(fun (%s : %s) -> %s)" parameter (string_of_sort sort)
        (string_of_term body)
  | Apply (function_, argument) ->
      Printf.sprintf "(%s %s)" (string_of_term function_)
        (string_of_term argument)
  | Not term -> Printf.sprintf "(not %s)" (string_of_term term)
  | And terms ->
      "(" ^ String.concat " && " (List.map string_of_term terms) ^ ")"
  | Or terms -> "(" ^ String.concat " || " (List.map string_of_term terms) ^ ")"
  | Equal (left, right) ->
      Printf.sprintf "(%s = %s)" (string_of_term left) (string_of_term right)
  | Add (left, right) ->
      Printf.sprintf "(%s + %s)" (string_of_term left) (string_of_term right)
  | Greater (left, right) ->
      Printf.sprintf "(%s > %s)" (string_of_term left) (string_of_term right)

let equal_sort = ( = )

let rec first_order_sort = function
  | Base _ -> true
  | Arrow (Base _, output) -> first_order_sort output
  | Arrow (Arrow _, _) -> false

let rec substitute_variable variable replacement term =
  match term with
  | Variable candidate when candidate = variable -> replacement
  | Lambda (parameter, sort, body) when parameter <> variable ->
      Lambda (parameter, sort, substitute_variable variable replacement body)
  | Apply (function_, argument) ->
      Apply
        ( substitute_variable variable replacement function_,
          substitute_variable variable replacement argument )
  | Not term -> Not (substitute_variable variable replacement term)
  | And terms -> And (List.map (substitute_variable variable replacement) terms)
  | Or terms -> Or (List.map (substitute_variable variable replacement) terms)
  | Equal (left, right) ->
      Equal
        ( substitute_variable variable replacement left,
          substitute_variable variable replacement right )
  | Add (left, right) ->
      Add
        ( substitute_variable variable replacement left,
          substitute_variable variable replacement right )
  | Greater (left, right) ->
      Greater
        ( substitute_variable variable replacement left,
          substitute_variable variable replacement right )
  | (Integer _ | Boolean _ | Variable _ | Generic _ | Evar _ | Lambda _) as term
    ->
      term

let rec normalize term =
  let normalize_application function_ argument =
    let function_ = normalize function_ in
    let argument = normalize argument in
    match function_ with
    | Lambda (parameter, _, body) ->
        normalize (substitute_variable parameter argument body)
    | _ -> Apply (function_, argument)
  in
  match term with
  | Apply (function_, argument) -> normalize_application function_ argument
  | Lambda (parameter, sort, body) -> Lambda (parameter, sort, normalize body)
  | Not term -> Not (normalize term)
  | And terms -> And (List.map normalize terms)
  | Or terms -> Or (List.map normalize terms)
  | Equal (left, right) -> Equal (normalize left, normalize right)
  | Add (left, right) -> Add (normalize left, normalize right)
  | Greater (left, right) -> Greater (normalize left, normalize right)
  | (Integer _ | Boolean _ | Variable _ | Generic _ | Evar _) as term -> term

let rec substitute_generic name replacement term =
  match term with
  | Generic candidate when candidate = name -> replacement
  | Lambda (parameter, sort, body) ->
      Lambda (parameter, sort, substitute_generic name replacement body)
  | Apply (function_, argument) ->
      Apply
        ( substitute_generic name replacement function_,
          substitute_generic name replacement argument )
  | Not term -> Not (substitute_generic name replacement term)
  | And terms -> And (List.map (substitute_generic name replacement) terms)
  | Or terms -> Or (List.map (substitute_generic name replacement) terms)
  | Equal (left, right) ->
      Equal
        ( substitute_generic name replacement left,
          substitute_generic name replacement right )
  | Add (left, right) ->
      Add
        ( substitute_generic name replacement left,
          substitute_generic name replacement right )
  | Greater (left, right) ->
      Greater
        ( substitute_generic name replacement left,
          substitute_generic name replacement right )
  | (Integer _ | Boolean _ | Variable _ | Generic _ | Evar _) as term -> term

let rec map_type_terms transform = function
  | Refined { base; index_sort; index; predicate } ->
      Refined
        {
          base;
          index_sort;
          index = transform index;
          predicate = transform predicate;
        }
  | Function (input, output) ->
      Function (map_type_terms transform input, map_type_terms transform output)

let substitute_generic_type name replacement =
  map_type_terms (substitute_generic name replacement)

let rec occurs_generic name = function
  | Generic candidate -> candidate = name
  | Lambda (_, _, body) | Not body -> occurs_generic name body
  | Apply (left, right)
  | Equal (left, right)
  | Add (left, right)
  | Greater (left, right) ->
      occurs_generic name left || occurs_generic name right
  | And terms | Or terms -> List.exists (occurs_generic name) terms
  | Integer _ | Boolean _ | Variable _ | Evar _ -> false

let rec value_dependent name polarity = function
  | Refined { index; _ } -> polarity = `Negative && occurs_generic name index
  | Function (input, output) ->
      value_dependent name
        (match polarity with `Positive -> `Negative | `Negative -> `Positive)
        input
      || value_dependent name polarity output

let rec infer_term_sort generics variables evars term =
  let infer = infer_term_sort generics variables evars in
  match term with
  | Integer _ -> Ok (Base Int)
  | Boolean _ -> Ok (Base Bool)
  | Variable variable -> (
      match List.assoc_opt variable variables with
      | Some sort -> Ok sort
      | None -> Error (Ill_sorted ("unbound refinement variable " ^ variable)))
  | Generic generic -> (
      match List.assoc_opt generic generics with
      | Some sort -> Ok sort
      | None -> Error (Ill_sorted ("unbound generic " ^ generic)))
  | Evar evar -> (
      match List.assoc_opt evar evars with
      | Some sort -> Ok sort
      | None -> Error (Ill_sorted ("unbound evar " ^ evar)))
  | Lambda (parameter, parameter_sort, body) ->
      Result.map
        (fun body_sort -> Arrow (parameter_sort, body_sort))
        (infer_term_sort generics
           ((parameter, parameter_sort) :: variables)
           evars body)
  | Apply (function_, argument) ->
      Result.bind (infer function_) (function
        | Arrow (parameter_sort, result_sort) ->
            Result.bind (infer argument) (fun argument_sort ->
                if equal_sort parameter_sort argument_sort then Ok result_sort
                else Error (Ill_sorted "refinement application sort mismatch"))
        | Base _ -> Error (Ill_sorted "applied a base-sorted refinement"))
  | Not term ->
      Result.bind (infer term) (fun sort ->
          if equal_sort sort (Base Bool) then Ok sort
          else Error (Ill_sorted "not expects bool"))
  | And terms | Or terms ->
      List.fold_left
        (fun result term ->
          Result.bind result (fun () ->
              Result.bind (infer term) (fun sort ->
                  if equal_sort sort (Base Bool) then Ok ()
                  else Error (Ill_sorted "boolean connective expects bool"))))
        (Ok ()) terms
      |> Result.map (fun () -> Base Bool)
  | Equal (left, right) ->
      Result.bind (infer left) (fun left_sort ->
          Result.bind (infer right) (fun right_sort ->
              if equal_sort left_sort right_sort then Ok (Base Bool)
              else Error (Ill_sorted "equality sort mismatch")))
  | Add (left, right) | Greater (left, right) ->
      Result.bind (infer left) (fun left_sort ->
          Result.bind (infer right) (fun right_sort ->
              if
                equal_sort left_sort (Base Int)
                && equal_sort right_sort (Base Int)
              then
                match term with
                | Add _ -> Ok (Base Int)
                | Greater _ -> Ok (Base Bool)
                | _ -> assert false
              else Error (Ill_sorted "arithmetic expects int")))

let rec check_type_sort generics = function
  | Refined { index_sort; index; predicate; _ } ->
      Result.bind (infer_term_sort generics [] [] index)
        (fun actual_index_sort ->
          if not (equal_sort actual_index_sort index_sort) then
            Error (Ill_sorted "base index has the wrong sort")
          else
            Result.bind (infer_term_sort generics [] [] predicate)
              (fun predicate_sort ->
                if equal_sort predicate_sort (Base Bool) then Ok ()
                else Error (Ill_sorted "refinement predicate must be bool")))
  | Function (input, output) ->
      Result.bind (check_type_sort generics input) (fun () ->
          check_type_sort generics output)

let well_formed scheme =
  let rec check generics hindley = function
    | Mono type_ ->
        Result.bind (check_type_sort generics type_) (fun () ->
            match
              List.find_opt
                (fun generic -> not (value_dependent generic `Positive type_))
                hindley
            with
            | None -> Ok ()
            | Some generic -> Error (Ill_formed_hindley generic))
    | Forall (generic, rest) ->
        if not (first_order_sort generic.sort) then
          Error
            (Ill_sorted
               ("generic " ^ generic.name
              ^ " has a non-first-order function sort"))
        else
          check
            ((generic.name, generic.sort) :: generics)
            (match generic.mode with
            | Hindley -> generic.name :: hindley
            | Horn -> hindley)
            rest
  in
  check [] [] scheme

module Evar_term = struct
  type t = term

  type head =
    | H_integer of int
    | H_boolean of bool
    | H_variable of string
    | H_generic of string
    | H_lambda of string * sort
    | H_apply
    | H_not
    | H_and of int
    | H_or of int
    | H_equal
    | H_add
    | H_greater

  let view = function
    | Evar evar -> `Variable evar
    | Integer integer -> `Node (H_integer integer, [])
    | Boolean boolean -> `Node (H_boolean boolean, [])
    | Variable variable -> `Node (H_variable variable, [])
    | Generic generic -> `Node (H_generic generic, [])
    | Lambda (parameter, sort, body) ->
        `Node (H_lambda (parameter, sort), [ body ])
    | Apply (function_, argument) -> `Node (H_apply, [ function_; argument ])
    | Not term -> `Node (H_not, [ term ])
    | And terms -> `Node (H_and (List.length terms), terms)
    | Or terms -> `Node (H_or (List.length terms), terms)
    | Equal (left, right) -> `Node (H_equal, [ left; right ])
    | Add (left, right) -> `Node (H_add, [ left; right ])
    | Greater (left, right) -> `Node (H_greater, [ left; right ])

  let make_node head children =
    match (head, children) with
    | H_integer integer, [] -> Integer integer
    | H_boolean boolean, [] -> Boolean boolean
    | H_variable variable, [] -> Variable variable
    | H_generic generic, [] -> Generic generic
    | H_lambda (parameter, sort), [ body ] -> Lambda (parameter, sort, body)
    | H_apply, [ function_; argument ] -> Apply (function_, argument)
    | H_not, [ term ] -> Not term
    | H_and arity, terms when arity = List.length terms -> And terms
    | H_or arity, terms when arity = List.length terms -> Or terms
    | H_equal, [ left; right ] -> Equal (left, right)
    | H_add, [ left; right ] -> Add (left, right)
    | H_greater, [ left; right ] -> Greater (left, right)
    | _ -> invalid_arg "invalid refinement term shape"

  let equal_head = ( = )
  let equal = ( = )
end

module Evars = Evar_context.Make (Evar_term)

let substitute_evars context term = Evars.substitute context term |> normalize
let substitute_evars_type context = map_type_terms (substitute_evars context)

let rec check_argument context actual formal constraints =
  match (actual, formal) with
  | ( Refined
        {
          base = actual_base;
          index_sort = actual_sort;
          index = actual_index;
          predicate = actual_predicate;
        },
      Refined
        {
          base = formal_base;
          index_sort = formal_sort;
          index = formal_index;
          predicate = formal_predicate;
        } ) -> (
      if actual_base <> formal_base || not (equal_sort actual_sort formal_sort)
      then Error (Type_mismatch "refined base types differ")
      else
        match Evars.unify context ~formal:formal_index ~actual:actual_index with
        | Error (Occurs (evar, _)) -> Error (Cyclic_instantiation evar)
        | Error (Shape_mismatch _) ->
            Error (Type_mismatch "generic indices do not unify")
        | Ok () ->
            Ok
              ({
                 assumption = substitute_evars context actual_predicate;
                 requirement = substitute_evars context formal_predicate;
               }
              :: constraints))
  | ( Function (actual_input, actual_output),
      Function (formal_input, formal_output) ) ->
      Result.bind (check_argument context formal_input actual_input constraints)
        (fun constraints ->
          check_argument context actual_output formal_output constraints)
  | _ -> Error (Type_mismatch "function and base types differ")

let elaborate_application scheme arguments =
  Result.bind (well_formed scheme) (fun () ->
      let arguments_well_sorted =
        List.fold_left
          (fun result argument ->
            Result.bind result (fun () -> check_type_sort [] argument))
          (Ok ()) arguments
      in
      Result.bind arguments_well_sorted (fun () ->
          let context = Evars.create () in
          let counter = ref 0 in
          let rec instantiate generics evar_sorts = function
            | Mono type_ -> Ok (generics, evar_sorts, type_)
            | Forall ({ mode = Horn; name; _ }, _) ->
                Error (Horn_not_supported name)
            | Forall ({ mode = Hindley; name; sort }, rest) ->
                let evar = Printf.sprintf "?%s_%d" name !counter in
                incr counter;
                let rest =
                  match rest with
                  | Mono type_ ->
                      Mono (substitute_generic_type name (Evar evar) type_)
                  | Forall _ as scheme ->
                      let rec substitute_scheme = function
                        | Mono type_ ->
                            Mono
                              (substitute_generic_type name (Evar evar) type_)
                        | Forall (generic, scheme) ->
                            Forall (generic, substitute_scheme scheme)
                      in
                      substitute_scheme scheme
                in
                instantiate ((name, evar) :: generics)
                  ((evar, sort) :: evar_sorts)
                  rest
          in
          Result.bind (instantiate [] [] scheme)
            (fun (generics, evar_sorts, type_) ->
              let rec apply type_ arguments constraints =
                match (arguments, type_) with
                | [], result -> Ok (result, constraints)
                | argument :: arguments, Function (parameter, result) ->
                    Result.bind
                      (check_argument context argument parameter constraints)
                      (fun constraints ->
                        apply
                          (substitute_evars_type context result)
                          arguments constraints)
                | _ :: _, Refined _ -> Error Arity_mismatch
              in
              Result.bind (apply type_ arguments [])
                (fun (result, constraints) ->
                  let rec collect = function
                    | [] -> Ok []
                    | (generic, evar) :: rest -> (
                        match Evars.solution context evar with
                        | None -> Error (Unsolved_hindley generic)
                        | Some refinement ->
                            let refinement =
                              substitute_evars context refinement
                            in
                            let expected_sort = List.assoc evar evar_sorts in
                            Result.bind
                              (infer_term_sort [] [] evar_sorts refinement)
                              (fun actual_sort ->
                                if not (equal_sort expected_sort actual_sort)
                                then
                                  Error
                                    (Ill_sorted
                                       ("instantiation of " ^ generic
                                      ^ " has the wrong sort"))
                                else
                                  Result.map
                                    (fun rest ->
                                      { generic; refinement } :: rest)
                                    (collect rest)))
                  in
                  match collect (List.rev generics) with
                  | Error error -> Error error
                  | Ok instantiations ->
                      Ok
                        {
                          instantiations;
                          result = substitute_evars_type context result;
                          constraints = List.rev constraints;
                        }))))
