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

val well_formed : scheme -> (unit, error) result
val elaborate_application : scheme -> type_ list -> (elaboration, error) result
val normalize : term -> term
val string_of_sort : sort -> string
val string_of_term : term -> string
