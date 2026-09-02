type symbol = { key : string; display : string }

type sort =
  | S_int
  | S_bool
  | S_unit
  | S_var of string
  | S_tuple of sort list
  | S_app of symbol * sort list
  | S_arrow of sort * sort

type constructor = { symbol : symbol; arguments : sort list; result : sort }

type datatype = {
  owner : sort;
  constructors : constructor list;
  native_smt : bool;
}

type logic_symbol = {
  logic_name : symbol;
  arguments : sort list;
  result : sort;
}

type quantifier = Forall | Exists

type axiom = {
  axiom_name : string;
  scope : string list;
  binders : (quantifier * string * sort) list;
  slice_roots : string list option;
  body : string;
  loc : Source_span.t;
}

type functor_theory = {
  functor_name : string;
  generative : bool;
  parameter_name : string;
  parameter_prefix : string;
  result_prefix : string;
  abstract_sorts : (string * sort) list;
  logic_symbols : (string * logic_symbol) list;
  axioms : axiom list;
  module_aliases : (string * string) list;
}

type pattern =
  | Pat_any
  | Pat_var of symbol
  | Pat_alias of pattern * symbol
  | Pat_int of int
  | Pat_bool of bool
  | Pat_tuple of sort * pattern list
  | Pat_construct of constructor * pattern list

type expr = {
  desc : expr_desc;
  sort : sort;
  refinement : Generic_refinement.type_ option;
  loc : Source_span.t;
}

and expr_desc =
  | Var of symbol
  | Int of int
  | Bool of bool
  | Tuple of expr list
  | Construct of constructor * expr list
  | Choose of expr list
  | Apply of symbol * expr list
  | Apply_value of expr * expr list
  | Lambda of (symbol * sort) list * expr
  | If of expr * expr * expr
  | Let of symbol * expr * expr
  | Match of expr * (pattern * expr) list
  | Record of constructor * expr list
  | Field of constructor * int * expr
  | Raise of symbol * expr option
  | Try of expr * (exception_pattern * expr) list
  | Ref of sort * expr
  | Let_ref of symbol * sort * expr * expr
  | Deref of symbol
  | Assign of symbol * expr
  | Sequence of expr * expr
  | Perform of symbol * expr option
  | Handle of expr * (symbol * symbol option * handler_action) list

and exception_pattern = Exn_any | Exn of symbol * symbol option

and handler_action =
  | Abort of expr
  | Resume of expr
  | Conditional of expr * handler_action * handler_action

type refined_base = {
  value_name : string;
  base_sort : sort;
  predicate : string;
}

type refined_type =
  | Refined_base of refined_base
  | Refined_arrow of {
      parameter : string;
      domain : refined_type;
      codomain : refined_type;
    }

type contract = {
  mode : Refined_types.mode;
  refined_type : refined_type;
  function_arity : int;
  result_state : string option;
  result_fresh : bool;
  result_references : (string * string) list;
  result_fresh_references : string list;
  result_reference_permissions : (string * string) list;
  result_recursive : bool;
  result_region : string option;
  requires_regions : (string * string) list;
  consumes_regions : string list;
  universals : string list;
  witnesses : (string * string) list;
  witness_relation : string option;
  ghosts : (string * sort) list;
  raises : (string * string) list;
  state : (string * string) list;
  modifies : string list;
  requires_state : (string * string) list;
  state_witnesses : (string * string) list;
  performs : (string * string) list;
  outcomes : coverage_outcome list;
  outcome_state : (string * string * string * string) list;
  outcome_modifies : (string * string * string) list;
  loc : Source_span.t;
}

and coverage_outcome = {
  kind : string;
  name : string;
  post : string;
  witnesses : (string * string) list;
  witness_relation : string option;
}

val rename_identifier : from:string -> into:string -> string -> string
val contract_domains : contract -> (string * refined_type) list
val contract_result : contract -> refined_type
val refined_sort : refined_type -> sort

type function_def = {
  symbol : symbol;
  arguments : (symbol * sort) list;
  result : sort;
  body : expr;
  contracts : contract list;
  measure : symbol list;
}

type registry = {
  constructors_by_uid : (string, constructor) Hashtbl.t;
  constructors_by_name : (string, constructor) Hashtbl.t;
  fields_by_uid : (string, constructor * int) Hashtbl.t;
  fields_by_name : (string, constructor * int) Hashtbl.t;
  logic_by_name : (string, logic_symbol) Hashtbl.t;
  abstract_sorts_by_name : (string, sort) Hashtbl.t;
  concrete_sorts_by_name : (string, sort) Hashtbl.t;
  choose_symbols : (string, unit) Hashtbl.t;
  module_aliases : (string, string) Hashtbl.t;
  functor_theories : (string, functor_theory) Hashtbl.t;
  generic_schemes_by_name : (string, Generic_refinement.scheme) Hashtbl.t;
  mutable axioms : axiom list;
  mutable lemmas : axiom list;
  mutable checked_lemmas : axiom list;
  mutable proof_artifacts : Refined_types.proof_artifact list;
  mutable datatype_templates : datatype list;
  mutable datatypes : datatype list;
}

type program = { registry : registry; functions : function_def list }
