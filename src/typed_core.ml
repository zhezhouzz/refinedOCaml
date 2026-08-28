type symbol = { key : string; display : string }

type sort =
  | S_int
  | S_bool
  | S_unit
  | S_var of string
  | S_tuple of sort list
  | S_app of symbol * sort list

type constructor = { symbol : symbol; arguments : sort list; result : sort }
type datatype = { owner : sort; constructors : constructor list }

type logic_symbol = {
  logic_name : symbol;
  arguments : sort list;
  result : sort;
}

type axiom = {
  axiom_name : string;
  scope : string list;
  variables : (string * sort) list;
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
  | If of expr * expr * expr
  | Let of symbol * expr * expr
  | Match of expr * (pattern * expr) list
  | Record of constructor * expr list
  | Field of constructor * int * expr
  | Raise of symbol * expr option
  | Try of expr * (exception_pattern * expr) list
  | Let_ref of symbol * sort * expr * expr
  | Deref of symbol
  | Assign of symbol * expr
  | Sequence of expr * expr
  | Perform of symbol * expr option
  | Handle of expr * (symbol * symbol option * handler_action) list

and exception_pattern = Exn_any | Exn of symbol * symbol option
and handler_action = Abort of expr | Resume of expr

type contract = {
  mode : Refined_types.mode;
  pre : string;
  post : string;
  witnesses : (string * string) list;
  raises : (string * string) list;
  state : (string * string) list;
  performs : (string * string) list;
  outcomes : coverage_outcome list;
  loc : Source_span.t;
}

and coverage_outcome = {
  kind : string;
  name : string;
  post : string;
  witnesses : (string * string) list;
}

type function_def = {
  symbol : symbol;
  arguments : (symbol * sort) list;
  result : sort;
  body : expr;
  contracts : contract list;
  measure : symbol option;
}

type registry = {
  constructors_by_uid : (string, constructor) Hashtbl.t;
  constructors_by_name : (string, constructor) Hashtbl.t;
  fields_by_uid : (string, constructor * int) Hashtbl.t;
  fields_by_name : (string, constructor * int) Hashtbl.t;
  logic_by_name : (string, logic_symbol) Hashtbl.t;
  abstract_sorts_by_name : (string, sort) Hashtbl.t;
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
