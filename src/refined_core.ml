open Parsetree
open Asttypes

type mode = Over | Under
type verdict = Valid | Invalid of string | Unknown of string

type obligation = {
  name : string;
  mode : mode;
  location : Location.t;
  smt : string;
  trusted_axioms : string list;
}

let mode_name = function Over -> "over" | Under -> "coverage"
let error ~loc format = Location.raise_errorf ~loc ("refinedOCaml: " ^^ format)

let smt_identifier name =
  String.map
    (function
      | ('a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_') as character -> character
      | _ -> '_')
    name

let longident_last id = Longident.last id

let string_constant expression =
  match expression.pexp_desc with
  | Pexp_constant { pconst_desc = Pconst_string (value, _, _); _ } -> value
  | _ -> error ~loc:expression.pexp_loc "contract fields must be strings"

let contract_of_attribute attribute =
  let mode =
    match attribute.attr_name.txt with
    | "refined.over" -> Some Over
    | "refined.under" | "refined.coverage" -> Some Under
    | _ -> None
  in
  match mode with
  | None -> None
  | Some mode -> (
      match attribute.attr_payload with
      | PStr
          [
            {
              pstr_desc =
                Pstr_eval ({ pexp_desc = Pexp_record (fields, None); _ }, _);
              _;
            };
          ] ->
          let find name =
            List.find_map
              (fun ({ txt; _ }, expression) ->
                if longident_last txt = name then
                  Some (string_constant expression)
                else None)
              fields
          in
          let required name =
            match find name with
            | Some value -> value
            | None ->
                error ~loc:attribute.attr_loc
                  "contract is missing the `%s` string field" name
          in
          Some (mode, required "pre", required "post")
      | _ ->
          error ~loc:attribute.attr_loc
            "expected [@%s { pre = \"...\"; post = \"...\" }]"
            attribute.attr_name.txt)

let app name arguments = "(" ^ String.concat " " (name :: arguments) ^ ")"

let and_ terms =
  match terms with [] -> "true" | [ term ] -> term | _ -> app "and" terms

let or_ terms =
  match terms with [] -> "false" | [ term ] -> term | _ -> app "or" terms

let binary_operator = function
  | "+" -> Some "+"
  | "-" -> Some "-"
  | "*" -> Some "*"
  | "/" -> Some "div"
  | "mod" -> Some "mod"
  | "=" -> Some "="
  | "<>" -> Some "distinct"
  | "<" -> Some "<"
  | "<=" -> Some "<="
  | ">" -> Some ">"
  | ">=" -> Some ">="
  | "&&" -> Some "and"
  | "||" -> Some "or"
  | "implies" -> Some "=>"
  | _ -> None

let parse_formula ~filename ~loc text =
  let lexbuf = Lexing.from_string text in
  Location.init lexbuf filename;
  try Parse.expression lexbuf
  with _ -> error ~loc "cannot parse refinement formula `%s`" text

(* Typedtree frontend -----------------------------------------------------

   The checker consumes the Typedtree emitted by OCaml, so all names and
   ordinary types have already been resolved by the real compiler. *)

module Typed_core = struct
  type symbol = { key : string; display : string }

  type sort =
    | S_int
    | S_bool
    | S_unit
    | S_var of string
    | S_tuple of sort list
    | S_app of symbol * sort list

  type constructor = { symbol : symbol; arguments : sort list }
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
    loc : Location.t;
  }

  type pattern =
    | Pat_any
    | Pat_var of symbol
    | Pat_alias of pattern * symbol
    | Pat_int of int
    | Pat_bool of bool
    | Pat_tuple of sort * pattern list
    | Pat_construct of constructor * pattern list

  type expr = { desc : expr_desc; sort : sort; loc : Location.t }

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

  type contract = { mode : mode; pre : string; post : string; loc : Location.t }

  type function_def = {
    symbol : symbol;
    arguments : (symbol * sort) list;
    result : sort;
    body : expr;
    contracts : contract list;
  }

  type registry = {
    constructors_by_uid : (string, constructor) Hashtbl.t;
    constructors_by_name : (string, constructor) Hashtbl.t;
    fields_by_uid : (string, constructor * int) Hashtbl.t;
    fields_by_name : (string, constructor * int) Hashtbl.t;
    logic_by_name : (string, logic_symbol) Hashtbl.t;
    mutable axioms : axiom list;
    mutable datatypes : datatype list;
  }

  type program = { registry : registry; functions : function_def list }
end

let typed_error ~loc format =
  Location.raise_errorf ~loc ("refinedOCaml typed frontend: " ^^ format)

let symbol_of_ident ?display ident =
  let name = Ident.name ident in
  Typed_core.
    {
      key = Ident.unique_name ident;
      display = Option.value display ~default:name;
    }

let symbol_of_path path =
  match path with
  | Path.Pident ident -> symbol_of_ident ident
  | _ ->
      let key = Path.name path in
      let display =
        match List.rev (String.split_on_char '.' key) with
        | name :: _ -> name
        | [] -> key
      in
      Typed_core.{ key; display }

let symbol_of_uid ~name uid =
  Typed_core.{ key = Format.asprintf "%a" Shape.Uid.print uid; display = name }

let uid_key uid = Format.asprintf "%a" Shape.Uid.print uid

let rec typed_sort_of_type type_expr =
  let open Typed_core in
  match Types.get_desc type_expr with
  | Types.Tconstr (path, _, _) when Path.same path Predef.path_int -> S_int
  | Types.Tconstr (path, _, _) when Path.same path Predef.path_bool -> S_bool
  | Types.Tconstr (path, _, _) when Path.same path Predef.path_unit -> S_unit
  | Types.Tconstr (path, arguments, _) when Path.same path Predef.path_list ->
      S_app
        ( { key = "list"; display = "list" },
          List.map typed_sort_of_type arguments )
  | Types.Tconstr (path, arguments, _) when Path.same path Predef.path_option ->
      S_app
        ( { key = "option"; display = "option" },
          List.map typed_sort_of_type arguments )
  | Types.Tconstr (path, arguments, _) ->
      S_app (symbol_of_path path, List.map typed_sort_of_type arguments)
  | Types.Ttuple elements -> S_tuple (List.map typed_sort_of_type elements)
  | Types.Tvar name | Types.Tunivar name ->
      let suffix =
        match name with
        | Some name -> smt_identifier name
        | None -> string_of_int (Types.get_id type_expr)
      in
      S_var ("a_" ^ suffix)
  | Types.Tpoly (body, _) -> typed_sort_of_type body
  | Types.Tlink body -> typed_sort_of_type body
  | Types.Tarrow _ ->
      typed_error ~loc:Location.none
        "higher-order values are not part of the MVP logical sort language"
  | Types.Tobject _ | Types.Tfield _ | Types.Tnil | Types.Tsubst _
  | Types.Tvariant _ | Types.Tpackage _ ->
      typed_error ~loc:Location.none
        "unsupported OCaml type in the MVP logical sort language"

let new_typed_registry () =
  Typed_core.
    {
      constructors_by_uid = Hashtbl.create 32;
      constructors_by_name = Hashtbl.create 32;
      fields_by_uid = Hashtbl.create 32;
      fields_by_name = Hashtbl.create 32;
      logic_by_name = Hashtbl.create 32;
      axioms = [];
      datatypes = [];
    }

let typed_register_constructor registry constructor uid name =
  Hashtbl.replace registry.Typed_core.constructors_by_uid (uid_key uid)
    constructor;
  Hashtbl.replace registry.Typed_core.constructors_by_name name constructor

let typed_register_types registry structure =
  let open Typed_core in
  let rec module_structure = function
    | { Typedtree.mod_desc = Typedtree.Tmod_structure structure; _ } ->
        Some structure
    | { mod_desc = Tmod_constraint (inner, _, _, _); _ } ->
        module_structure inner
    | _ -> None
  in
  let rec visit_structure structure =
    List.iter
      (fun item ->
        match item.Typedtree.str_desc with
        | Typedtree.Tstr_type (_, declarations) ->
            List.iter register declarations
        | Tstr_module binding ->
            Option.iter visit_structure (module_structure binding.mb_expr)
        | Tstr_recmodule bindings ->
            List.iter
              (fun (binding : Typedtree.module_binding) ->
                Option.iter visit_structure (module_structure binding.mb_expr))
              bindings
        | _ -> ())
      structure.Typedtree.str_items
  and register declaration =
    if declaration.Typedtree.typ_params <> [] then ()
    else
      let owner_symbol =
        symbol_of_ident ~display:declaration.typ_name.txt declaration.typ_id
      in
      let owner = S_app (owner_symbol, []) in
      match declaration.typ_kind with
      | Typedtree.Ttype_variant declarations ->
          let constructors =
            List.map
              (fun typed_constructor ->
                let arguments =
                  match typed_constructor.Typedtree.cd_args with
                  | Cstr_tuple types ->
                      List.map
                        (fun (core_type : Typedtree.core_type) ->
                          typed_sort_of_type core_type.ctyp_type)
                        types
                  | Cstr_record labels ->
                      List.map
                        (fun (label : Typedtree.label_declaration) ->
                          typed_sort_of_type label.Typedtree.ld_type.ctyp_type)
                        labels
                in
                let constructor =
                  {
                    symbol =
                      symbol_of_uid ~name:typed_constructor.cd_name.txt
                        typed_constructor.cd_uid;
                    arguments;
                  }
                in
                typed_register_constructor registry constructor
                  typed_constructor.cd_uid typed_constructor.cd_name.txt;
                constructor)
              declarations
          in
          registry.datatypes <- { owner; constructors } :: registry.datatypes
      | Ttype_record labels ->
          let arguments =
            List.map
              (fun label ->
                typed_sort_of_type label.Typedtree.ld_type.ctyp_type)
              labels
          in
          let constructor =
            {
              symbol =
                {
                  key = owner_symbol.key ^ ".record";
                  display = "record_" ^ declaration.typ_name.txt;
                };
              arguments;
            }
          in
          List.iteri
            (fun index (label : Typedtree.label_declaration) ->
              Hashtbl.replace registry.fields_by_uid (uid_key label.ld_uid)
                (constructor, index);
              Hashtbl.replace registry.fields_by_name label.ld_name.txt
                (constructor, index))
            labels;
          registry.datatypes <-
            { owner; constructors = [ constructor ] } :: registry.datatypes
      | Ttype_abstract | Ttype_open -> ()
  in
  visit_structure structure

let typed_lookup_constructor registry ~loc uid name =
  match
    Hashtbl.find_opt registry.Typed_core.constructors_by_uid (uid_key uid)
  with
  | Some constructor -> constructor
  | None ->
      typed_error ~loc "constructor `%s` is outside the supported datatype set"
        name

let rec typed_pattern registry (pattern : Typedtree.pattern) =
  let open Typed_core in
  match pattern.pat_desc with
  | Typedtree.Tpat_any -> Pat_any
  | Tpat_var (ident, name, _) ->
      Pat_var (symbol_of_ident ~display:name.txt ident)
  | Tpat_alias (inner, ident, name, _) ->
      Pat_alias
        (typed_pattern registry inner, symbol_of_ident ~display:name.txt ident)
  | Tpat_constant (Const_int value) -> Pat_int value
  | Tpat_construct (name, _, _, _) when name.txt = Longident.Lident "true" ->
      Pat_bool true
  | Tpat_construct (name, _, _, _) when name.txt = Longident.Lident "false" ->
      Pat_bool false
  | Tpat_construct (_, description, patterns, _) ->
      let constructor =
        typed_lookup_constructor registry ~loc:pattern.pat_loc
          description.cstr_uid description.cstr_name
      in
      Pat_construct (constructor, List.map (typed_pattern registry) patterns)
  | Tpat_tuple patterns ->
      Pat_tuple
        ( typed_sort_of_type pattern.pat_type,
          List.map (typed_pattern registry) patterns )
  | _ -> typed_error ~loc:pattern.pat_loc "unsupported pattern in the MVP Core"

let value_pattern_of_computation ~loc pattern =
  match pattern.Typedtree.pat_desc with
  | Typedtree.Tpat_value value -> (value :> Typedtree.pattern)
  | _ ->
      typed_error ~loc "exception/effect patterns are not part of the MVP Core"

let typed_field registry ~loc description =
  match
    Hashtbl.find_opt registry.Typed_core.fields_by_uid
      (uid_key description.Types.lbl_uid)
  with
  | Some entry -> entry
  | None ->
      typed_error ~loc "record field `%s` is outside the supported datatype set"
        description.lbl_name

let rec typed_expression registry (expression : Typedtree.expression) =
  let open Typed_core in
  let make desc =
    {
      desc;
      sort = typed_sort_of_type expression.exp_type;
      loc = expression.exp_loc;
    }
  in
  let recurse = typed_expression registry in
  match expression.exp_desc with
  | Typedtree.Texp_ident (path, _, _) -> make (Var (symbol_of_path path))
  | Texp_constant (Const_int value) -> make (Int value)
  | Texp_construct (name, _, []) when name.txt = Longident.Lident "true" ->
      make (Bool true)
  | Texp_construct (name, _, []) when name.txt = Longident.Lident "false" ->
      make (Bool false)
  | Texp_construct (_, description, arguments) ->
      let constructor =
        typed_lookup_constructor registry ~loc:expression.exp_loc
          description.cstr_uid description.cstr_name
      in
      make (Construct (constructor, List.map recurse arguments))
  | Texp_tuple expressions -> make (Tuple (List.map recurse expressions))
  | Texp_apply ({ exp_desc = Texp_ident (path, _, description); _ }, arguments)
    ->
      let arguments =
        List.map
          (function
            | Nolabel, Some argument -> recurse argument
            | _, Some _ ->
                typed_error ~loc:expression.exp_loc
                  "labelled applications are not part of the MVP Core"
            | _, None ->
                typed_error ~loc:expression.exp_loc
                  "partial labelled applications are not part of the MVP Core")
          arguments
      in
      if
        List.exists
          (fun attribute ->
            attribute.Parsetree.attr_name.txt = "refined.choose")
          description.Types.val_attributes
      then make (Choose arguments)
      else make (Apply (symbol_of_path path, arguments))
  | Texp_ifthenelse (condition, if_true, Some if_false) ->
      make (If (recurse condition, recurse if_true, recurse if_false))
  | Texp_let (Nonrecursive, [ binding ], body) -> (
      match binding.vb_pat.pat_desc with
      | Tpat_var (ident, name, _) ->
          make
            (Let
               ( symbol_of_ident ~display:name.txt ident,
                 recurse binding.vb_expr,
                 recurse body ))
      | _ ->
          typed_error ~loc:binding.vb_loc
            "local let bindings currently require a variable pattern")
  | Texp_match (scrutinee, cases, [], Total) ->
      let cases =
        List.map
          (fun (case : Typedtree.computation Typedtree.case) ->
            if Option.is_some case.c_guard then
              typed_error ~loc:case.c_rhs.exp_loc
                "guarded matches are not part of the MVP Core";
            let pattern =
              value_pattern_of_computation ~loc:case.c_lhs.pat_loc case.c_lhs
            in
            (typed_pattern registry pattern, recurse case.c_rhs))
          cases
      in
      make (Match (recurse scrutinee, cases))
  | Texp_match (_, _, _, Partial) ->
      typed_error ~loc:expression.exp_loc
        "partial matches are rejected by the refinement frontend"
  | Texp_record { fields; extended_expression = None; _ } ->
      let entries =
        Array.to_list fields
        |> List.filter_map (fun (description, definition) ->
            match definition with
            | Typedtree.Overridden (_, value) ->
                let constructor, index =
                  typed_field registry ~loc:value.exp_loc description
                in
                Some (constructor, index, recurse value)
            | Kept _ -> None)
      in
      let constructor =
        match entries with
        | (constructor, _, _) :: _ -> constructor
        | [] -> typed_error ~loc:expression.exp_loc "empty record literal"
      in
      let values =
        List.init (List.length constructor.arguments) (fun index ->
            match
              List.find_opt (fun (_, current, _) -> current = index) entries
            with
            | Some (_, _, value) -> value
            | None ->
                typed_error ~loc:expression.exp_loc
                  "record literal is missing a field")
      in
      make (Record (constructor, values))
  | Texp_field (record, _, description) ->
      let constructor, index =
        typed_field registry ~loc:expression.exp_loc description
      in
      make (Field (constructor, index, recurse record))
  | _ ->
      typed_error ~loc:expression.exp_loc
        "unsupported Typedtree expression in the MVP Core"

let typed_contracts attributes =
  List.filter_map
    (fun attribute ->
      match contract_of_attribute attribute with
      | None -> None
      | Some (mode, pre, post) ->
          Some Typed_core.{ mode; pre; post; loc = attribute.attr_loc })
    attributes

let typed_normalize expression =
  let open Typed_core in
  let counter = ref 0 in
  let fresh sort loc =
    let index = !counter in
    incr counter;
    let symbol =
      { key = "refined_anf_" ^ string_of_int index; display = "_anf" }
    in
    (symbol, { desc = Var symbol; sort; loc })
  in
  let rec atoms expressions continuation =
    match expressions with
    | [] -> continuation []
    | expression :: rest ->
        anf expression (fun atom ->
            atoms rest (fun atoms -> continuation (atom :: atoms)))
  and bind_operation original desc continuation =
    let operation = { original with desc } in
    let symbol, variable = fresh original.sort original.loc in
    let body = continuation variable in
    {
      desc = Let (symbol, operation, body);
      sort = body.sort;
      loc = original.loc;
    }
  and anf expression continuation =
    match expression.desc with
    | Var _ | Int _ | Bool _ -> continuation expression
    | Let (symbol, value, body) ->
        anf value (fun value ->
            let body = anf body continuation in
            {
              desc = Let (symbol, value, body);
              sort = body.sort;
              loc = expression.loc;
            })
    | If (condition, if_true, if_false) ->
        anf condition (fun condition ->
            let if_true = anf if_true continuation in
            let if_false = anf if_false continuation in
            {
              desc = If (condition, if_true, if_false);
              sort = if_true.sort;
              loc = expression.loc;
            })
    | Match (scrutinee, cases) ->
        anf scrutinee (fun scrutinee ->
            let cases =
              List.map
                (fun (pattern, body) -> (pattern, anf body continuation))
                cases
            in
            let result_sort =
              match cases with
              | (_, body) :: _ -> body.sort
              | [] -> expression.sort
            in
            {
              desc = Match (scrutinee, cases);
              sort = result_sort;
              loc = expression.loc;
            })
    | Tuple expressions ->
        atoms expressions (fun expressions ->
            bind_operation expression (Tuple expressions) continuation)
    | Construct (constructor, expressions) ->
        atoms expressions (fun expressions ->
            bind_operation expression
              (Construct (constructor, expressions))
              continuation)
    | Record (constructor, expressions) ->
        atoms expressions (fun expressions ->
            bind_operation expression
              (Record (constructor, expressions))
              continuation)
    | Choose expressions ->
        atoms expressions (fun expressions ->
            bind_operation expression (Choose expressions) continuation)
    | Apply (symbol, expressions) ->
        atoms expressions (fun expressions ->
            bind_operation expression (Apply (symbol, expressions)) continuation)
    | Field (constructor, index, record) ->
        anf record (fun record ->
            bind_operation expression
              (Field (constructor, index, record))
              continuation)
  in
  anf expression Fun.id

let typed_bound_variable (pattern : Typedtree.pattern) =
  match pattern.pat_desc with
  | Typedtree.Tpat_var (ident, name, _) ->
      Some
        ( symbol_of_ident ~display:name.txt ident,
          typed_sort_of_type pattern.pat_type )
  | Tpat_alias ({ pat_desc = Tpat_any; _ }, ident, name, _) ->
      Some
        ( symbol_of_ident ~display:name.txt ident,
          typed_sort_of_type pattern.pat_type )
  | _ -> None

let typed_function registry binding =
  let open Typed_core in
  let contracts = typed_contracts binding.Typedtree.vb_attributes in
  match binding.vb_expr.exp_desc with
  | Typedtree.Texp_function (parameters, Tfunction_body body) ->
      let symbol =
        match binding.vb_pat.pat_desc with
        | Typedtree.Tpat_var (ident, name, _) ->
            symbol_of_ident ~display:name.txt ident
        | _ ->
            if contracts = [] then
              typed_error ~loc:binding.vb_pat.pat_loc
                "top-level functions in the MVP Core must have a simple \
                 variable name"
            else
              typed_error ~loc:binding.vb_pat.pat_loc
                "a refined top-level binding must have a simple variable name"
      in
      let arguments =
        List.map
          (fun (parameter : Typedtree.function_param) ->
            match parameter.fp_kind with
            | Tparam_pat pattern -> (
                match typed_bound_variable pattern with
                | Some binding -> binding
                | None ->
                    typed_error ~loc:parameter.fp_loc
                      "function parameters in the MVP Core must be simple \
                       variables")
            | _ ->
                typed_error ~loc:parameter.fp_loc
                  "function parameters in the MVP Core must be simple variables")
          parameters
      in
      let argument_names =
        List.map
          (fun ((symbol : Typed_core.symbol), _) -> symbol.display)
          arguments
      in
      if
        List.length argument_names
        <> List.length (List.sort_uniq String.compare argument_names)
      then
        typed_error ~loc:binding.vb_loc
          "refined function parameters must have distinct source names";
      Some
        {
          symbol;
          arguments;
          result = typed_sort_of_type body.exp_type;
          body = typed_normalize (typed_expression registry body);
          contracts;
        }
  | _ ->
      if contracts = [] then None
      else
        typed_error ~loc:binding.vb_expr.exp_loc
          "a refined binding must be an explicitly written function"

let attribute_named name attribute = attribute.Parsetree.attr_name.txt = name
let qualified_name scope name = String.concat "." (scope @ [ name ])

let rec longident_name = function
  | Longident.Lident name -> name
  | Ldot (prefix, name) -> longident_name prefix ^ "." ^ name
  | Lapply (left, right) ->
      longident_name left ^ "(" ^ longident_name right ^ ")"

let rec arrow_sorts type_expr =
  match Types.get_desc type_expr with
  | Types.Tarrow (_, argument, result, _) ->
      let arguments, final = arrow_sorts result in
      (typed_sort_of_type argument :: arguments, final)
  | Types.Tpoly (body, _) | Types.Tlink body -> arrow_sorts body
  | _ -> ([], typed_sort_of_type type_expr)

let rec logic_sort_of_core_type core_type =
  let open Typed_core in
  match core_type.Parsetree.ptyp_desc with
  | Ptyp_constr ({ txt; _ }, arguments) -> (
      let name = longident_name txt in
      let arguments = List.map logic_sort_of_core_type arguments in
      match (name, arguments) with
      | "int", [] -> S_int
      | "bool", [] -> S_bool
      | "unit", [] -> S_unit
      | "list", [ argument ] ->
          S_app ({ key = "list"; display = "list" }, [ argument ])
      | "option", [ argument ] ->
          S_app ({ key = "option"; display = "option" }, [ argument ])
      | _ -> S_app ({ key = name; display = name }, arguments))
  | Ptyp_var name -> S_var ("a_" ^ smt_identifier name)
  | Ptyp_tuple elements -> S_tuple (List.map logic_sort_of_core_type elements)
  | _ -> typed_error ~loc:core_type.ptyp_loc "unsupported sort in theory axiom"

let logic_sort_of_string ~loc text =
  let lexbuf = Lexing.from_string text in
  Location.init lexbuf loc.Location.loc_start.pos_fname;
  try logic_sort_of_core_type (Parse.core_type lexbuf)
  with _ -> typed_error ~loc "cannot parse logical sort `%s`" text

let rec expression_list expression =
  match expression.Parsetree.pexp_desc with
  | Pexp_construct ({ txt = Lident "[]"; _ }, None) -> []
  | Pexp_construct
      ( { txt = Lident "::"; _ },
        Some { pexp_desc = Pexp_tuple [ head; tail ]; _ } ) ->
      head :: expression_list tail
  | _ -> typed_error ~loc:expression.pexp_loc "expected an OCaml list literal"

let axiom_of_attribute scope attribute =
  if not (attribute_named "refined.axiom" attribute) then None
  else
    match attribute.attr_payload with
    | PStr
        [
          {
            pstr_desc =
              Pstr_eval ({ pexp_desc = Pexp_record (fields, None); _ }, _);
            _;
          };
        ] ->
        let find name =
          List.find_map
            (fun ({ txt; _ }, value) ->
              if longident_last txt = name then Some value else None)
            fields
        in
        let required name =
          match find name with
          | Some value -> value
          | None ->
              typed_error ~loc:attribute.attr_loc "axiom is missing field `%s`"
                name
        in
        let name = string_constant (required "name") in
        let body = string_constant (required "body") in
        let variables =
          expression_list (required "vars")
          |> List.map (fun expression ->
              match expression.pexp_desc with
              | Pexp_tuple [ name; sort ] ->
                  ( string_constant name,
                    logic_sort_of_string ~loc:sort.pexp_loc
                      (string_constant sort) )
              | _ ->
                  typed_error ~loc:expression.pexp_loc
                    "axiom vars must contain (name, sort) string pairs")
        in
        Some
          Typed_core.
            {
              axiom_name = qualified_name scope name;
              scope;
              variables;
              body;
              loc = attribute.attr_loc;
            }
    | _ ->
        typed_error ~loc:attribute.attr_loc
          "expected [@@@refined.axiom { name; vars; body }]"

let register_logic_symbol registry scope binding =
  if
    not
      (List.exists
         (attribute_named "refined.predicate")
         binding.Typedtree.vb_attributes)
  then ()
  else
    let name, ident =
      match binding.vb_pat.pat_desc with
      | Typedtree.Tpat_var (ident, name, _) -> (name.txt, ident)
      | _ ->
          typed_error ~loc:binding.vb_pat.pat_loc
            "a logical predicate binding must have a simple name"
    in
    let arguments, result = arrow_sorts binding.vb_expr.exp_type in
    if result <> Typed_core.S_bool then
      typed_error ~loc:binding.vb_loc "logical predicate `%s` must return bool"
        name;
    let full_name = qualified_name scope name in
    let logic_symbol =
      Typed_core.
        {
          logic_name = { key = "logic." ^ full_name; display = name };
          arguments;
          result;
        }
    in
    ignore ident;
    Hashtbl.replace registry.Typed_core.logic_by_name full_name logic_symbol;
    if not (Hashtbl.mem registry.logic_by_name name) then
      Hashtbl.add registry.logic_by_name name logic_symbol

let register_logic_value registry scope
    (description : Typedtree.value_description) =
  if
    not
      (List.exists
         (attribute_named "refined.predicate")
         description.val_attributes)
  then ()
  else
    let name = description.val_name.txt in
    let arguments, result = arrow_sorts description.val_val.Types.val_type in
    if result <> Typed_core.S_bool then
      typed_error ~loc:description.val_loc
        "logical predicate `%s` must return bool" name;
    let full_name = qualified_name scope name in
    let logic_symbol =
      Typed_core.
        {
          logic_name = { key = "logic." ^ full_name; display = name };
          arguments;
          result;
        }
    in
    Hashtbl.replace registry.Typed_core.logic_by_name full_name logic_symbol;
    if not (Hashtbl.mem registry.logic_by_name name) then
      Hashtbl.add registry.logic_by_name name logic_symbol

let typed_register_theories registry structure =
  let rec module_structure = function
    | { Typedtree.mod_desc = Typedtree.Tmod_structure structure; _ } ->
        Some structure
    | { mod_desc = Tmod_constraint (inner, _, _, _); _ } ->
        module_structure inner
    | _ -> None
  in
  let rec visit scope structure =
    List.iter
      (fun item ->
        match item.Typedtree.str_desc with
        | Typedtree.Tstr_value (_, bindings) ->
            List.iter (register_logic_symbol registry scope) bindings
        | Tstr_attribute attribute ->
            Option.iter
              (fun axiom ->
                registry.Typed_core.axioms <-
                  axiom :: registry.Typed_core.axioms)
              (axiom_of_attribute scope attribute)
        | Tstr_module binding ->
            let scope =
              match binding.mb_name.txt with
              | Some name -> scope @ [ name ]
              | None -> scope
            in
            Option.iter (visit scope) (module_structure binding.mb_expr)
        | Tstr_recmodule bindings ->
            List.iter
              (fun (binding : Typedtree.module_binding) ->
                let nested =
                  match binding.mb_name.txt with
                  | Some name -> scope @ [ name ]
                  | None -> scope
                in
                Option.iter (visit nested) (module_structure binding.mb_expr))
              bindings
        | _ -> ())
      structure.Typedtree.str_items
  in
  visit [] structure

let typed_register_signature_theories registry ~root signature =
  let rec visit_module_type scope module_type =
    match module_type.Typedtree.mty_desc with
    | Typedtree.Tmty_signature signature -> visit scope signature
    | Tmty_with (inner, _) -> visit_module_type scope inner
    | _ -> ()
  and visit scope signature =
    List.iter
      (fun item ->
        match item.Typedtree.sig_desc with
        | Typedtree.Tsig_value description ->
            register_logic_value registry scope description
        | Tsig_attribute attribute ->
            Option.iter
              (fun axiom ->
                registry.Typed_core.axioms <-
                  axiom :: registry.Typed_core.axioms)
              (axiom_of_attribute scope attribute)
        | Tsig_module declaration ->
            let nested =
              match declaration.md_name.txt with
              | Some name -> scope @ [ name ]
              | None -> scope
            in
            visit_module_type nested declaration.md_type
        | Tsig_recmodule declarations ->
            List.iter
              (fun (declaration : Typedtree.module_declaration) ->
                let nested =
                  match declaration.md_name.txt with
                  | Some name -> scope @ [ name ]
                  | None -> scope
                in
                visit_module_type nested declaration.md_type)
              declarations
        | _ -> ())
      signature.Typedtree.sig_items
  in
  visit [ root ] signature

let typed_program_of_structure ?registry structure =
  let registry = Option.value registry ~default:(new_typed_registry ()) in
  typed_register_types registry structure;
  typed_register_theories registry structure;
  let rec module_structure = function
    | { Typedtree.mod_desc = Typedtree.Tmod_structure structure; _ } ->
        Some structure
    | { mod_desc = Tmod_constraint (inner, _, _, _); _ } ->
        module_structure inner
    | _ -> None
  in
  let rec functions structure =
    List.concat_map
      (fun item ->
        match item.Typedtree.str_desc with
        | Typedtree.Tstr_value (_, bindings) ->
            List.filter_map (typed_function registry) bindings
        | Tstr_module binding ->
            Option.fold ~none:[] ~some:functions
              (module_structure binding.mb_expr)
        | Tstr_recmodule bindings ->
            List.concat_map
              (fun (binding : Typedtree.module_binding) ->
                Option.fold ~none:[] ~some:functions
                  (module_structure binding.mb_expr))
              bindings
        | _ -> [])
      structure.Typedtree.str_items
  in
  Typed_core.{ registry; functions = functions structure }

type typed_rmi = {
  format_version : int;
  ocaml_version : string;
  unit_name : string;
  interface_digest : string option;
  logic_symbols : (string * Typed_core.logic_symbol) list;
  axioms : Typed_core.axiom list;
}

let current_rmi_version = 1

let read_rmi path =
  let channel = open_in_bin path in
  let rmi : typed_rmi =
    Fun.protect
      ~finally:(fun () -> close_in channel)
      (fun () -> Marshal.from_channel channel)
  in
  if rmi.format_version <> current_rmi_version then
    typed_error ~loc:Location.none "unsupported .rmi format version in `%s`"
      path;
  if rmi.ocaml_version <> Sys.ocaml_version then
    typed_error ~loc:Location.none
      ".rmi `%s` was produced by OCaml %s, but the checker uses OCaml %s" path
      rmi.ocaml_version Sys.ocaml_version;
  rmi

let write_rmi ~cmti ~output =
  let cmt = Cmt_format.read_cmt cmti in
  let signature =
    match cmt.cmt_annots with
    | Cmt_format.Interface signature -> signature
    | _ ->
        typed_error ~loc:Location.none "`%s` is not a complete .cmti interface"
          cmti
  in
  let registry = new_typed_registry () in
  typed_register_signature_theories registry ~root:cmt.cmt_modname signature;
  let seen = Hashtbl.create 16 in
  let logic_symbols =
    Hashtbl.fold
      (fun name (logic_symbol : Typed_core.logic_symbol) entries ->
        if
          logic_symbol.logic_name.key = "logic." ^ name
          && not (Hashtbl.mem seen logic_symbol.logic_name.key)
        then (
          Hashtbl.add seen logic_symbol.logic_name.key ();
          (name, logic_symbol) :: entries)
        else entries)
      registry.logic_by_name []
  in
  let rmi =
    {
      format_version = current_rmi_version;
      ocaml_version = Sys.ocaml_version;
      unit_name = cmt.cmt_modname;
      interface_digest = Option.map Digest.to_hex cmt.cmt_interface_digest;
      logic_symbols;
      axioms = List.rev registry.axioms;
    }
  in
  let channel = open_out_bin output in
  Fun.protect
    ~finally:(fun () -> close_out channel)
    (fun () -> Marshal.to_channel channel rmi [])

let load_rmi_into registry cmt path =
  let rmi = read_rmi path in
  let imported = List.assoc_opt rmi.unit_name cmt.Cmt_format.cmt_imports in
  (match imported with
  | None ->
      typed_error ~loc:Location.none
        "theory `%s` belongs to module `%s`, which this implementation does \
         not import"
        path rmi.unit_name
  | Some _ -> ());
  let imported_digest = Option.join imported |> Option.map Digest.to_hex in
  (match (rmi.interface_digest, imported_digest) with
  | Some expected, Some actual when expected <> actual ->
      typed_error ~loc:Location.none
        "stale theory `%s`: interface digest does not match the imported .cmi"
        path
  | _ -> ());
  List.iter
    (fun (name, logic_symbol) ->
      Hashtbl.replace registry.Typed_core.logic_by_name name logic_symbol;
      let short = logic_symbol.Typed_core.logic_name.display in
      if not (Hashtbl.mem registry.logic_by_name short) then
        Hashtbl.add registry.logic_by_name short logic_symbol)
    rmi.logic_symbols;
  registry.axioms <- List.rev_append rmi.axioms registry.axioms

let typed_smt_sort =
  let rec translate = function
    | Typed_core.S_int -> "Int"
    | S_bool -> "Bool"
    | S_unit -> "Unit"
    | S_var name -> "Tvar_" ^ smt_identifier name
    | S_tuple elements ->
        "Tuple_"
        ^ String.concat "_"
            (List.map (fun sort -> smt_identifier (translate sort)) elements)
    | S_app (symbol, arguments) ->
        let suffix =
          match arguments with
          | [] -> ""
          | _ ->
              "_"
              ^ String.concat "_"
                  (List.map
                     (fun sort -> smt_identifier (translate sort))
                     arguments)
        in
        "T_" ^ smt_identifier symbol.key ^ suffix
  in
  translate

let typed_constructor_name (constructor : Typed_core.constructor) =
  "C_" ^ smt_identifier constructor.Typed_core.symbol.key

let typed_recognizer (constructor : Typed_core.constructor) =
  "is_" ^ typed_constructor_name constructor

let typed_selector (constructor : Typed_core.constructor) index =
  Printf.sprintf "sel_%s_%d" (typed_constructor_name constructor) index

let typed_tuple_constructor sort = "mk_" ^ typed_smt_sort sort

let typed_tuple_selector sort index =
  Printf.sprintf "sel_%s_%d" (typed_smt_sort sort) index

let typed_logic_name (logic_symbol : Typed_core.logic_symbol) =
  "L_" ^ smt_identifier logic_symbol.logic_name.key

let typed_lookup_logic registry scope name =
  let rec candidates scope =
    match scope with
    | [] -> [ name ]
    | _ ->
        qualified_name scope name
        :: candidates (List.rev (List.tl (List.rev scope)))
  in
  let names = if String.contains name '.' then [ name ] else candidates scope in
  List.find_map
    (fun candidate ->
      Hashtbl.find_opt registry.Typed_core.logic_by_name candidate)
    names

let typed_specialize_program (program : Typed_core.program)
    (function_def : Typed_core.function_def) pre_expression post_expression =
  let open Typed_core in
  let substitutions = Hashtbl.create 8 in
  let rec substitute = function
    | Typed_core.S_var name as sort -> (
        match Hashtbl.find_opt substitutions name with
        | Some sort -> sort
        | None -> sort)
    | S_tuple sorts -> S_tuple (List.map substitute sorts)
    | S_app (symbol, sorts) -> S_app (symbol, List.map substitute sorts)
    | (S_int | S_bool | S_unit) as sort -> sort
  in
  let rec unify ~loc formal actual =
    match (formal, actual) with
    | Typed_core.S_var name, actual -> (
        match Hashtbl.find_opt substitutions name with
        | None -> Hashtbl.add substitutions name actual
        | Some previous when previous = actual -> ()
        | Some previous ->
            typed_error ~loc
              "one obligation instantiates type variable `%s` as both %s and %s"
              name (typed_smt_sort previous) (typed_smt_sort actual))
    | S_tuple formals, S_tuple actuals
      when List.length formals = List.length actuals ->
        List.iter2 (unify ~loc) formals actuals
    | S_app (formal_symbol, formals), S_app (actual_symbol, actuals)
      when formal_symbol.key = actual_symbol.key
           && List.length formals = List.length actuals ->
        List.iter2 (unify ~loc) formals actuals
    | S_int, S_int | S_bool, S_bool | S_unit, S_unit -> ()
    | _ ->
        typed_error ~loc
          "logical predicate type mismatch: expected %s but got %s"
          (typed_smt_sort formal) (typed_smt_sort actual)
  in
  let formula_env =
    List.map
      (fun (symbol, sort) -> (symbol.Typed_core.display, sort))
      function_def.arguments
  in
  let rec infer_formula scope env expression =
    let recurse = infer_formula scope env in
    match expression.Parsetree.pexp_desc with
    | Pexp_ident { txt; _ } -> (
        let name = longident_name txt in
        match List.assoc_opt name env with
        | Some sort -> sort
        | None ->
            typed_error ~loc:expression.pexp_loc "unknown logical variable `%s`"
              name)
    | Pexp_constant { pconst_desc = Pconst_integer _; _ } -> Typed_core.S_int
    | Pexp_construct ({ txt = Lident ("true" | "false"); _ }, None) -> S_bool
    | Pexp_construct ({ txt; _ }, _) -> (
        let name = longident_last txt in
        match Hashtbl.find_opt program.registry.constructors_by_name name with
        | Some constructor -> (
            match
              List.find_opt
                (fun (datatype : Typed_core.datatype) ->
                  List.exists
                    (fun (candidate : Typed_core.constructor) ->
                      candidate.symbol.key = constructor.Typed_core.symbol.key)
                    datatype.constructors)
                program.registry.datatypes
            with
            | Some datatype -> datatype.owner
            | None ->
                typed_error ~loc:expression.pexp_loc
                  "constructor `%s` has no registered owner" name)
        | None ->
            typed_error ~loc:expression.pexp_loc "unknown constructor `%s`" name
        )
    | Pexp_apply ({ pexp_desc = Pexp_ident { txt; _ }; _ }, arguments) -> (
        let name = longident_name txt in
        let argument_sorts =
          List.map
            (function
              | Nolabel, argument -> recurse argument
              | _ ->
                  typed_error ~loc:expression.pexp_loc
                    "logical applications cannot use labels")
            arguments
        in
        match binary_operator name with
        | Some ("+" | "-" | "*" | "div" | "mod") ->
            List.iter (unify ~loc:expression.pexp_loc S_int) argument_sorts;
            S_int
        | Some _ -> S_bool
        | None -> (
            match typed_lookup_logic program.registry scope name with
            | Some logic_symbol ->
                if
                  List.length argument_sorts
                  <> List.length logic_symbol.arguments
                then
                  typed_error ~loc:expression.pexp_loc
                    "logical predicate `%s` expects %d arguments" name
                    (List.length logic_symbol.arguments);
                List.iter2
                  (unify ~loc:expression.pexp_loc)
                  logic_symbol.arguments argument_sorts;
                substitute logic_symbol.result
            | None ->
                typed_error ~loc:expression.pexp_loc
                  "unknown logical predicate `%s`" name))
    | Pexp_field (record, { txt; _ }) -> (
        ignore (recurse record);
        let name = longident_last txt in
        match Hashtbl.find_opt program.registry.fields_by_name name with
        | Some (constructor, index) ->
            List.nth constructor.Typed_core.arguments index
        | None ->
            typed_error ~loc:expression.pexp_loc "unknown record field `%s`"
              name)
    | _ -> typed_error ~loc:expression.pexp_loc "unsupported refinement formula"
  in
  let rec infer_core expression =
    let recurse = infer_core in
    match expression.Typed_core.desc with
    | Apply (symbol, arguments) ->
        List.iter recurse arguments;
        Option.iter
          (fun (logic_symbol : Typed_core.logic_symbol) ->
            if
              List.length arguments
              <> List.length logic_symbol.Typed_core.arguments
            then
              typed_error ~loc:expression.loc
                "logical predicate `%s` has an unsupported application arity"
                symbol.display;
            List.iter2
              (fun formal (actual : Typed_core.expr) ->
                unify ~loc:actual.Typed_core.loc formal actual.sort)
              logic_symbol.arguments arguments)
          (typed_lookup_logic program.registry [] symbol.key)
    | Tuple expressions | Choose expressions -> List.iter recurse expressions
    | Construct (_, expressions) | Record (_, expressions) ->
        List.iter recurse expressions
    | If (condition, if_true, if_false) ->
        List.iter recurse [ condition; if_true; if_false ]
    | Let (_, value, body) ->
        recurse value;
        recurse body
    | Match (scrutinee, cases) ->
        recurse scrutinee;
        List.iter (fun (_, body) -> recurse body) cases
    | Field (_, _, record) -> recurse record
    | Var _ | Int _ | Bool _ -> ()
  in
  ignore (infer_formula [] formula_env pre_expression);
  ignore
    (infer_formula []
       (("result", function_def.result) :: formula_env)
       post_expression);
  infer_core function_def.body;
  if Hashtbl.length substitutions = 0 then program
  else
    let logic_by_name =
      Hashtbl.create (Hashtbl.length program.registry.logic_by_name)
    in
    Hashtbl.iter
      (fun name (logic_symbol : Typed_core.logic_symbol) ->
        let arguments = List.map substitute logic_symbol.arguments in
        let result = substitute logic_symbol.result in
        let suffix =
          String.concat "_"
            (List.map
               (fun sort -> smt_identifier (typed_smt_sort sort))
               arguments)
        in
        let logic_name =
          {
            logic_symbol.logic_name with
            key = logic_symbol.logic_name.key ^ ".instance." ^ suffix;
          }
        in
        Hashtbl.replace logic_by_name name { logic_name; arguments; result })
      program.registry.logic_by_name;
    let axioms =
      List.map
        (fun (axiom : Typed_core.axiom) ->
          {
            axiom with
            variables =
              List.map
                (fun (name, sort) -> (name, substitute sort))
                axiom.variables;
          })
        program.registry.axioms
    in
    let registry = { program.registry with logic_by_name; axioms } in
    { program with registry }

let typed_formula ?(scope = []) registry env expression =
  let rec translate env expression =
    let recurse = translate env in
    match expression.Parsetree.pexp_desc with
    | Pexp_ident { txt; _ } -> (
        let name = longident_name txt in
        match List.assoc_opt name env with
        | Some term -> term
        | None -> (
            match typed_lookup_logic registry scope name with
            | Some logic_symbol when logic_symbol.arguments = [] ->
                typed_logic_name logic_symbol
            | _ ->
                typed_error ~loc:expression.pexp_loc
                  "unknown logical variable `%s`" name))
    | Pexp_constant { pconst_desc = Pconst_integer (value, _); _ } -> value
    | Pexp_construct ({ txt = Lident "true"; _ }, None) -> "true"
    | Pexp_construct ({ txt = Lident "false"; _ }, None) -> "false"
    | Pexp_construct ({ txt; _ }, argument) ->
        let name = longident_last txt in
        let constructor =
          match
            Hashtbl.find_opt registry.Typed_core.constructors_by_name name
          with
          | Some constructor -> constructor
          | None ->
              typed_error ~loc:expression.pexp_loc "unknown constructor `%s`"
                name
        in
        let arguments =
          match argument with
          | None -> []
          | Some { pexp_desc = Pexp_tuple expressions; _ } ->
              List.map recurse expressions
          | Some expression -> [ recurse expression ]
        in
        if arguments = [] then typed_constructor_name constructor
        else app (typed_constructor_name constructor) arguments
    | Pexp_apply
        ( { pexp_desc = Pexp_ident { txt = Lident "not"; _ }; _ },
          [ (Nolabel, argument) ] ) ->
        app "not" [ recurse argument ]
    | Pexp_apply ({ pexp_desc = Pexp_ident { txt; _ }; _ }, arguments) -> (
        let name = longident_name txt in
        let arguments =
          List.map
            (function
              | Nolabel, argument -> recurse argument
              | _ ->
                  typed_error ~loc:expression.pexp_loc
                    "logical applications cannot use labels")
            arguments
        in
        match (binary_operator name, arguments) with
        | Some operator, [ left; right ] -> app operator [ left; right ]
        | _ -> (
            match typed_lookup_logic registry scope name with
            | Some logic_symbol ->
                if List.length arguments <> List.length logic_symbol.arguments
                then
                  typed_error ~loc:expression.pexp_loc
                    "logical predicate `%s` expects %d arguments" name
                    (List.length logic_symbol.arguments);
                app (typed_logic_name logic_symbol) arguments
            | None ->
                typed_error ~loc:expression.pexp_loc
                  "unknown logical predicate `%s`" name))
    | Pexp_field (record, { txt; _ }) ->
        let name = longident_last txt in
        let constructor, index =
          match Hashtbl.find_opt registry.fields_by_name name with
          | Some entry -> entry
          | None ->
              typed_error ~loc:expression.pexp_loc
                "unknown logical record field `%s`" name
        in
        app (typed_selector constructor index) [ recurse record ]
    | _ -> typed_error ~loc:expression.pexp_loc "unsupported refinement formula"
  in
  translate env expression

let typed_pattern_smt env scrutinee pattern =
  let rec translate env scrutinee = function
    | Typed_core.Pat_any -> ("true", env)
    | Pat_var symbol -> ("true", (symbol.key, scrutinee) :: env)
    | Pat_alias (inner, symbol) ->
        let guard, env = translate env scrutinee inner in
        (guard, (symbol.key, scrutinee) :: env)
    | Pat_int value -> (app "=" [ scrutinee; string_of_int value ], env)
    | Pat_bool value -> (app "=" [ scrutinee; string_of_bool value ], env)
    | Pat_tuple (sort, patterns) ->
        let guards, env =
          List.fold_left2
            (fun (guards, env) index pattern ->
              let guard, env =
                translate env
                  (app (typed_tuple_selector sort index) [ scrutinee ])
                  pattern
              in
              (guard :: guards, env))
            ([], env)
            (List.init (List.length patterns) Fun.id)
            patterns
        in
        (and_ guards, env)
    | Pat_construct (constructor, patterns) ->
        let guards, env =
          List.fold_left2
            (fun (guards, env) index pattern ->
              let guard, env =
                translate env
                  (app (typed_selector constructor index) [ scrutinee ])
                  pattern
              in
              (guard :: guards, env))
            ([], env)
            (List.init (List.length patterns) Fun.id)
            patterns
        in
        (and_ (app (typed_recognizer constructor) [ scrutinee ] :: guards), env)
  in
  translate env scrutinee pattern

let rec typed_expr_smt_with_choices (program : Typed_core.program) call_stack
    choices env expression =
  let registry = program.registry in
  let _sort = expression.Typed_core.sort in
  let recurse = typed_expr_smt_with_choices program call_stack choices env in
  match expression.Typed_core.desc with
  | Var symbol -> (
      match List.assoc_opt symbol.key env with
      | Some term -> term
      | None ->
          typed_error ~loc:expression.loc "unsupported global value `%s`"
            symbol.display)
  | Int value -> string_of_int value
  | Bool value -> string_of_bool value
  | Construct (constructor, arguments) | Record (constructor, arguments) ->
      let arguments = List.map recurse arguments in
      if arguments = [] then typed_constructor_name constructor
      else app (typed_constructor_name constructor) arguments
  | Choose [ left; right ] ->
      let name = "choice_" ^ string_of_int (List.length !choices) in
      choices := (name, Typed_core.S_bool) :: !choices;
      app "ite" [ name; recurse left; recurse right ]
  | Choose _ ->
      typed_error ~loc:expression.loc
        "the MVP choose primitive currently requires exactly two alternatives"
  | Apply (symbol, [ left; right ]) -> (
      match binary_operator symbol.display with
      | Some operator -> app operator [ recurse left; recurse right ]
      | None -> (
          match typed_lookup_logic registry [] symbol.key with
          | Some logic_symbol ->
              if List.length logic_symbol.arguments <> 2 then
                typed_error ~loc:expression.loc
                  "logical predicate `%s` has an unsupported application arity"
                  symbol.display;
              app
                (typed_logic_name logic_symbol)
                [ recurse left; recurse right ]
          | None ->
              typed_inline_call program call_stack choices env expression symbol
                [ left; right ]))
  | Apply (symbol, [ argument ]) when symbol.display = "not" ->
      app "not" [ recurse argument ]
  | Apply (symbol, _) -> (
      let arguments =
        match expression.desc with
        | Apply (_, arguments) -> arguments
        | _ -> assert false
      in
      match typed_lookup_logic registry [] symbol.key with
      | Some logic_symbol ->
          if List.length arguments <> List.length logic_symbol.arguments then
            typed_error ~loc:expression.loc
              "logical predicate `%s` has an unsupported application arity"
              symbol.display;
          app (typed_logic_name logic_symbol) (List.map recurse arguments)
      | None ->
          typed_inline_call program call_stack choices env expression symbol
            arguments)
  | If (condition, if_true, if_false) ->
      app "ite" [ recurse condition; recurse if_true; recurse if_false ]
  | Let (symbol, value, body) ->
      let value = recurse value in
      typed_expr_smt_with_choices program call_stack choices
        ((symbol.key, value) :: env)
        body
  | Match (scrutinee, cases) ->
      let scrutinee = recurse scrutinee in
      let translated =
        List.map
          (fun (pattern, body) ->
            let guard, case_env = typed_pattern_smt env scrutinee pattern in
            ( guard,
              typed_expr_smt_with_choices program call_stack choices case_env
                body ))
          cases
      in
      let rec tree = function
        | [] -> typed_error ~loc:expression.loc "empty match"
        | [ (_, body) ] -> body
        | (guard, body) :: rest -> app "ite" [ guard; body; tree rest ]
      in
      tree translated
  | Field (constructor, index, record) ->
      app (typed_selector constructor index) [ recurse record ]
  | Tuple elements ->
      app (typed_tuple_constructor expression.sort) (List.map recurse elements)

and typed_inline_call program call_stack choices env expression symbol arguments
    =
  let function_def =
    List.find_opt
      (fun (function_def : Typed_core.function_def) ->
        function_def.symbol.key = symbol.Typed_core.key)
      program.Typed_core.functions
  in
  match function_def with
  | None ->
      typed_error ~loc:expression.Typed_core.loc
        "call to `%s` needs a refinement summary" symbol.display
  | Some function_def ->
      if List.mem symbol.key call_stack then
        typed_error ~loc:expression.loc
          "recursive call to `%s` requires a measure/summary" symbol.display;
      if List.length arguments <> List.length function_def.arguments then
        typed_error ~loc:expression.loc
          "call to `%s` has unsupported partial arity" symbol.display;
      let terms =
        List.map
          (typed_expr_smt_with_choices program call_stack choices env)
          arguments
      in
      let call_env =
        List.map2
          (fun (argument, _) term -> (argument.Typed_core.key, term))
          function_def.arguments terms
      in
      typed_expr_smt_with_choices program (symbol.key :: call_stack) choices
        call_env function_def.body

let typed_expr_smt program env expression =
  let choices = ref [] in
  let term = typed_expr_smt_with_choices program [] choices env expression in
  (term, List.rev !choices)

let typed_collect_sorts program function_def =
  let module Set = Set.Make (String) in
  let rec add set sort =
    let set = Set.add (typed_smt_sort sort) set in
    match sort with
    | Typed_core.S_tuple sorts | S_app (_, sorts) ->
        List.fold_left add set sorts
    | S_int | S_bool | S_unit | S_var _ -> set
  in
  let set =
    List.fold_left
      (fun set (_, sort) -> add set sort)
      Set.empty function_def.Typed_core.arguments
  in
  let set = add set function_def.result in
  let set =
    Hashtbl.fold
      (fun _ (logic_symbol : Typed_core.logic_symbol) set ->
        let set = List.fold_left add set logic_symbol.arguments in
        add set logic_symbol.result)
      program.Typed_core.registry.logic_by_name set
  in
  let set =
    List.fold_left
      (fun set (axiom : Typed_core.axiom) ->
        List.fold_left (fun set (_, sort) -> add set sort) set axiom.variables)
      set program.registry.axioms
  in
  List.fold_left
    (fun set (datatype : Typed_core.datatype) ->
      let set = add set datatype.Typed_core.owner in
      List.fold_left
        (fun set (constructor : Typed_core.constructor) ->
          List.fold_left add set constructor.Typed_core.arguments)
        set datatype.constructors)
    set program.Typed_core.registry.datatypes
  |> Set.elements

let typed_collect_sort_values program function_def =
  let values = Hashtbl.create 32 in
  let rec add sort =
    Hashtbl.replace values (typed_smt_sort sort) sort;
    match sort with
    | Typed_core.S_tuple sorts | S_app (_, sorts) -> List.iter add sorts
    | S_int | S_bool | S_unit | S_var _ -> ()
  in
  List.iter (fun (_, sort) -> add sort) function_def.Typed_core.arguments;
  add function_def.result;
  List.iter
    (fun (datatype : Typed_core.datatype) ->
      add datatype.owner;
      List.iter
        (fun (constructor : Typed_core.constructor) ->
          List.iter add constructor.arguments)
        datatype.constructors)
    program.Typed_core.registry.datatypes;
  Hashtbl.iter
    (fun _ (logic_symbol : Typed_core.logic_symbol) ->
      List.iter add logic_symbol.arguments;
      add logic_symbol.result)
    program.registry.logic_by_name;
  List.iter
    (fun (axiom : Typed_core.axiom) ->
      List.iter (fun (_, sort) -> add sort) axiom.variables)
    program.registry.axioms;
  Hashtbl.fold (fun _ sort result -> sort :: result) values []

let typed_datatype_prelude program function_def =
  let buffer = Buffer.create 4096 in
  let line format =
    Printf.kbprintf (fun _ -> Buffer.add_char buffer '\n') buffer format
  in
  let datatype_sort_names =
    List.map
      (fun (datatype : Typed_core.datatype) ->
        typed_smt_sort datatype.Typed_core.owner)
      program.Typed_core.registry.datatypes
  in
  typed_collect_sorts program function_def
  |> List.iter (fun sort ->
      if
        sort <> "Int" && sort <> "Bool"
        && not (List.mem sort datatype_sort_names)
      then line "(declare-sort %s 0)" sort);
  typed_collect_sort_values program function_def
  |> List.iter (function
    | Typed_core.S_tuple elements as tuple_sort ->
        let tuple_name = typed_smt_sort tuple_sort in
        let constructor = typed_tuple_constructor tuple_sort in
        line "(declare-fun %s (%s) %s)" constructor
          (String.concat " " (List.map typed_smt_sort elements))
          tuple_name;
        List.iteri
          (fun index sort ->
            line "(declare-fun %s (%s) %s)"
              (typed_tuple_selector tuple_sort index)
              tuple_name (typed_smt_sort sort))
          elements;
        let arguments =
          List.mapi
            (fun index sort -> ("t" ^ string_of_int index, sort))
            elements
        in
        let binders =
          "("
          ^ String.concat " "
              (List.map
                 (fun (name, sort) ->
                   Printf.sprintf "(%s %s)" name (typed_smt_sort sort))
                 arguments)
          ^ ")"
        in
        let constructed = app constructor (List.map fst arguments) in
        List.iteri
          (fun index _ ->
            line "(assert (forall %s (= (%s %s) %s)))" binders
              (typed_tuple_selector tuple_sort index)
              constructed
              (fst (List.nth arguments index)))
          elements;
        let fields =
          List.mapi
            (fun index _ -> app (typed_tuple_selector tuple_sort index) [ "v" ])
            elements
        in
        line "(assert (forall ((v %s)) (= v %s)))" tuple_name
          (app constructor fields)
    | _ -> ());
  List.iter
    (fun (datatype : Typed_core.datatype) ->
      line "(declare-sort %s 0)" (typed_smt_sort datatype.Typed_core.owner))
    program.registry.datatypes;
  let declared_logic = Hashtbl.create 16 in
  Hashtbl.iter
    (fun _ (logic_symbol : Typed_core.logic_symbol) ->
      let name = typed_logic_name logic_symbol in
      if not (Hashtbl.mem declared_logic name) then (
        Hashtbl.add declared_logic name ();
        line "(declare-fun %s (%s) %s)" name
          (String.concat " " (List.map typed_smt_sort logic_symbol.arguments))
          (typed_smt_sort logic_symbol.result)))
    program.registry.logic_by_name;
  List.rev program.registry.axioms
  |> List.iter (fun (axiom : Typed_core.axiom) ->
      let formula =
        parse_formula ~filename:axiom.loc.loc_start.pos_fname ~loc:axiom.loc
          axiom.body
      in
      let env =
        List.map (fun (name, _) -> (name, smt_identifier name)) axiom.variables
      in
      let body =
        typed_formula ~scope:axiom.scope program.registry env formula
      in
      let binders =
        "("
        ^ String.concat " "
            (List.map
               (fun (name, sort) ->
                 Printf.sprintf "(%s %s)" (smt_identifier name)
                   (typed_smt_sort sort))
               axiom.variables)
        ^ ")"
      in
      let assertion =
        if axiom.variables = [] then body else app "forall" [ binders; body ]
      in
      line "; trusted axiom: %s" axiom.axiom_name;
      line "(assert %s)" assertion);
  List.iter
    (fun (datatype : Typed_core.datatype) ->
      let result = typed_smt_sort datatype.Typed_core.owner in
      List.iter
        (fun (constructor : Typed_core.constructor) ->
          line "(declare-fun %s (%s) %s)"
            (typed_constructor_name constructor)
            (String.concat " "
               (List.map typed_smt_sort constructor.Typed_core.arguments))
            result;
          line "(declare-fun %s (%s) Bool)"
            (typed_recognizer constructor)
            result;
          List.iteri
            (fun index sort ->
              line "(declare-fun %s (%s) %s)"
                (typed_selector constructor index)
                result (typed_smt_sort sort))
            constructor.arguments)
        datatype.constructors)
    program.registry.datatypes;
  List.iter
    (fun (datatype : Typed_core.datatype) ->
      let result = typed_smt_sort datatype.Typed_core.owner in
      List.iter
        (fun (constructor : Typed_core.constructor) ->
          let arguments =
            List.mapi
              (fun index sort -> ("a" ^ string_of_int index, sort))
              constructor.Typed_core.arguments
          in
          let terms = List.map fst arguments in
          let value =
            if terms = [] then typed_constructor_name constructor
            else app (typed_constructor_name constructor) terms
          in
          let quantify formula =
            if arguments = [] then formula
            else
              app "forall"
                [
                  "("
                  ^ String.concat " "
                      (List.map
                         (fun (name, sort) ->
                           Printf.sprintf "(%s %s)" name (typed_smt_sort sort))
                         arguments)
                  ^ ")";
                  formula;
                ]
          in
          line "(assert %s)"
            (quantify (app (typed_recognizer constructor) [ value ]));
          List.iteri
            (fun index _ ->
              line "(assert %s)"
                (quantify
                   (app "="
                      [
                        app (typed_selector constructor index) [ value ];
                        List.nth terms index;
                      ])))
            constructor.arguments;
          List.iter
            (fun (other : Typed_core.constructor) ->
              if other.Typed_core.symbol.key <> constructor.symbol.key then
                line "(assert %s)"
                  (quantify
                     (app "not" [ app (typed_recognizer other) [ value ] ])))
            datatype.constructors)
        datatype.constructors;
      line "(assert (forall ((v %s)) %s))" result
        (or_
           (List.map
              (fun (constructor : Typed_core.constructor) ->
                app (typed_recognizer constructor) [ "v" ])
              datatype.constructors));
      List.iter
        (fun (constructor : Typed_core.constructor) ->
          let fields =
            List.mapi
              (fun index _ -> app (typed_selector constructor index) [ "v" ])
              constructor.Typed_core.arguments
          in
          let rebuilt =
            if fields = [] then typed_constructor_name constructor
            else app (typed_constructor_name constructor) fields
          in
          line "(assert (forall ((v %s)) (=> (%s v) (= v %s))))" result
            (typed_recognizer constructor)
            rebuilt)
        datatype.constructors)
    program.registry.datatypes;
  Buffer.contents buffer

let typed_binder (symbol, sort) =
  Printf.sprintf "(%s %s)"
    (smt_identifier symbol.Typed_core.key)
    (typed_smt_sort sort)

type typed_vc_context = {
  program : Typed_core.program;
  function_def : Typed_core.function_def;
  formula_env : (string * string) list;
  body : string;
  choices : (string * Typed_core.sort) list;
  pre : string;
  post_expression : Parsetree.expression;
  buffer : Buffer.t;
}

module type Typed_semantics = sig
  val mode : mode
  val encode : typed_vc_context -> unit
end

module Safety_semantics : Typed_semantics = struct
  let mode = Over

  let encode context =
    let post =
      typed_formula context.program.registry
        (("result", "result") :: context.formula_env)
        context.post_expression
    in
    List.iter
      (fun argument ->
        Buffer.add_string context.buffer
          (Printf.sprintf "(declare-const %s %s)\n"
             (smt_identifier (fst argument).Typed_core.key)
             (typed_smt_sort (snd argument))))
      context.function_def.arguments;
    List.iter
      (fun (name, sort) ->
        Buffer.add_string context.buffer
          (Printf.sprintf "(declare-const %s %s)\n" name (typed_smt_sort sort)))
      context.choices;
    Buffer.add_string context.buffer
      (Printf.sprintf "(assert %s)\n" context.pre);
    Buffer.add_string context.buffer
      (Printf.sprintf "(assert (not (let ((result %s)) %s)))\n" context.body
         post)
end

module Coverage_semantics : Typed_semantics = struct
  let mode = Under

  let encode context =
    let missing = "missing_result" in
    let post =
      typed_formula context.program.registry
        [ ("result", missing) ]
        context.post_expression
    in
    let choice_binders =
      List.map
        (fun (name, sort) ->
          Printf.sprintf "(%s %s)" name (typed_smt_sort sort))
        context.choices
    in
    let quantified =
      "("
      ^ String.concat " "
          (List.map typed_binder context.function_def.arguments @ choice_binders)
      ^ ")"
    in
    Buffer.add_string context.buffer
      (Printf.sprintf "(declare-const %s %s)\n" missing
         (typed_smt_sort context.function_def.result));
    Buffer.add_string context.buffer (Printf.sprintf "(assert %s)\n" post);
    Buffer.add_string context.buffer
      (Printf.sprintf "(assert (forall %s (not %s)))\n" quantified
         (and_ [ context.pre; app "=" [ missing; context.body ] ]))
end

let typed_semantics = function
  | Over -> (module Safety_semantics : Typed_semantics)
  | Under -> (module Coverage_semantics : Typed_semantics)

let typed_obligation (program : Typed_core.program)
    (function_def : Typed_core.function_def) (contract : Typed_core.contract) =
  let env =
    List.map
      (fun (symbol, _) -> (symbol.Typed_core.key, smt_identifier symbol.key))
      function_def.Typed_core.arguments
  in
  let formula_env =
    List.map2
      (fun (symbol, _) (_, term) -> (symbol.Typed_core.display, term))
      function_def.arguments env
  in
  let pre_expression =
    parse_formula ~filename:contract.loc.loc_start.pos_fname ~loc:contract.loc
      contract.pre
  in
  let post_expression =
    parse_formula ~filename:contract.loc.loc_start.pos_fname ~loc:contract.loc
      contract.post
  in
  let program =
    typed_specialize_program program function_def pre_expression post_expression
  in
  let body, choices = typed_expr_smt program env function_def.body in
  let pre = typed_formula program.registry formula_env pre_expression in
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer
    "(set-option :produce-models true)\n(set-logic ALL)\n";
  Buffer.add_string buffer (typed_datatype_prelude program function_def);
  let module Semantics = (val typed_semantics contract.mode : Typed_semantics)
  in
  if Semantics.mode <> contract.mode then assert false;
  Semantics.encode
    {
      program;
      function_def;
      formula_env;
      body;
      choices;
      pre;
      post_expression;
      buffer;
    };
  Buffer.add_string buffer "(check-sat)\n(get-model)\n";
  {
    name = function_def.symbol.display;
    mode = contract.mode;
    location = contract.loc;
    smt = Buffer.contents buffer;
    trusted_axioms =
      List.rev_map
        (fun (axiom : Typed_core.axiom) -> axiom.axiom_name)
        program.registry.axioms;
  }

let obligations_of_cmt_with_theories ~theories filename =
  let cmt = Cmt_format.read_cmt filename in
  match cmt.cmt_annots with
  | Cmt_format.Implementation structure ->
      let registry = new_typed_registry () in
      List.iter (load_rmi_into registry cmt) theories;
      let program = typed_program_of_structure ~registry structure in
      List.concat_map
        (fun function_def ->
          List.map
            (typed_obligation program function_def)
            function_def.Typed_core.contracts)
        program.functions
  | Cmt_format.Interface _ ->
      typed_error ~loc:Location.none
        "interface theory loading is not implemented in the first Typedtree \
         slice"
  | Packed _ | Partial_implementation _ | Partial_interface _ ->
      typed_error ~loc:Location.none "expected a complete implementation .cmt"

let obligations_of_cmt filename =
  obligations_of_cmt_with_theories ~theories:[] filename

let read_all channel =
  let buffer = Buffer.create 1024 in
  (try
     while true do
       Buffer.add_string buffer (input_line channel);
       Buffer.add_char buffer '\n'
     done
   with End_of_file -> ());
  Buffer.contents buffer

let solve obligation =
  let input, output, error =
    Unix.open_process_full "z3 -in -T:10" (Unix.environment ())
  in
  output_string output obligation.smt;
  close_out output;
  let stdout = read_all input in
  let stderr = read_all error in
  ignore (Unix.close_process_full (input, output, error));
  let first_line =
    match String.split_on_char '\n' stdout with
    | line :: _ -> String.trim line
    | [] -> ""
  in
  match first_line with
  | "unsat" -> Valid
  | "sat" -> Invalid stdout
  | "unknown" -> Unknown (stdout ^ stderr)
  | _ -> Unknown (stdout ^ stderr)
