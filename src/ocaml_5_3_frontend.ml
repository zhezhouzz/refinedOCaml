open Refined_ir
open Refined_common
open Parsetree
open Asttypes

let supported_ocaml_version = "5.3.0"

let ensure_supported_version () =
  if Sys.ocaml_version <> supported_ocaml_version then
    Location.raise_errorf ~loc:Location.none
      "refinedOCaml frontend supports OCaml %s, but is running under OCaml %s"
      supported_ocaml_version Sys.ocaml_version

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
      generic_schemes_by_name = Hashtbl.create 16;
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

let surface_record ~loc expression =
  match expression.Parsetree.pexp_desc with
  | Pexp_record (fields, None) -> fields
  | _ -> typed_error ~loc "expected a record payload"

let surface_field fields name =
  List.find_map
    (fun ({ txt; _ }, value) ->
      if longident_last txt = name then Some value else None)
    fields

let surface_required ~loc fields name =
  match surface_field fields name with
  | Some value -> value
  | None -> typed_error ~loc "surface refinement is missing field `%s`" name

let rec surface_list expression =
  match expression.Parsetree.pexp_desc with
  | Pexp_construct ({ txt = Lident "[]"; _ }, None) -> []
  | Pexp_construct
      ( { txt = Lident "::"; _ },
        Some { pexp_desc = Pexp_tuple [ head; tail ]; _ } ) ->
      head :: surface_list tail
  | _ -> typed_error ~loc:expression.pexp_loc "expected an OCaml list literal"

let rec generic_sort_of_core_type core_type =
  let open Generic_refinement in
  match core_type.Parsetree.ptyp_desc with
  | Ptyp_constr ({ txt; _ }, []) -> (
      match longident_name txt with
      | "int" -> Base Int
      | "bool" -> Base Bool
      | "unit" -> Base Unit
      | name -> Base (Named name))
  | Ptyp_arrow (Nolabel, input, output) ->
      Arrow (generic_sort_of_core_type input, generic_sort_of_core_type output)
  | _ ->
      typed_error ~loc:core_type.ptyp_loc
        "generic refinement sorts are first-order named sorts and arrows"

let generic_sort_of_string ~loc text =
  let lexbuf = Lexing.from_string text in
  Location.init lexbuf loc.Location.loc_start.pos_fname;
  try generic_sort_of_core_type (Parse.core_type lexbuf)
  with _ -> typed_error ~loc "cannot parse generic refinement sort `%s`" text

let generic_term_of_string ~loc ~generics ~expected_sort text =
  let open Generic_refinement in
  let lexbuf = Lexing.from_string text in
  Location.init lexbuf loc.Location.loc_start.pos_fname;
  let expression =
    try Parse.expression lexbuf
    with _ -> typed_error ~loc "cannot parse refinement term `%s`" text
  in
  let rec pattern_parameter expected pattern =
    match pattern.Parsetree.ppat_desc with
    | Ppat_var name -> (name.txt, expected)
    | Ppat_constraint ({ ppat_desc = Ppat_var name; _ }, core_type) ->
        (name.txt, generic_sort_of_core_type core_type)
    | _ ->
        typed_error ~loc:pattern.ppat_loc
          "refinement lambdas require a variable parameter"
  and translate expected expression =
    let recurse = translate None in
    match expression.Parsetree.pexp_desc with
    | Pexp_constant { pconst_desc = Pconst_integer (integer, _); _ } ->
        Integer (int_of_string integer)
    | Pexp_construct ({ txt = Lident "true"; _ }, None) -> Boolean true
    | Pexp_construct ({ txt = Lident "false"; _ }, None) -> Boolean false
    | Pexp_ident { txt; _ } ->
        let name = longident_name txt in
        if List.mem name generics then Generic name else Variable name
    | Pexp_function
        ( [ { pparam_desc = Pparam_val (Nolabel, None, pattern); _ } ],
          _,
          Pfunction_body body ) ->
        let parameter_sort =
          match expected with
          | Some (Arrow (input, _)) -> input
          | _ -> Base (Named "_")
        in
        let parameter, parameter_sort =
          pattern_parameter parameter_sort pattern
        in
        Lambda (parameter, parameter_sort, translate None body)
    | Pexp_apply
        ( { pexp_desc = Pexp_ident { txt = Lident "not"; _ }; _ },
          [ (Nolabel, argument) ] ) ->
        Not (recurse argument)
    | Pexp_apply
        ( { pexp_desc = Pexp_ident { txt; _ }; _ },
          [ (Nolabel, left); (Nolabel, right) ] ) -> (
        match longident_name txt with
        | "&&" -> And [ recurse left; recurse right ]
        | "||" -> Or [ recurse left; recurse right ]
        | "=" -> Equal (recurse left, recurse right)
        | "+" -> Add (recurse left, recurse right)
        | ">" -> Greater (recurse left, recurse right)
        | _ -> Apply (recurse left, recurse right))
    | Pexp_apply (function_, [ (Nolabel, argument) ]) ->
        Apply (recurse function_, recurse argument)
    | _ ->
        typed_error ~loc:expression.pexp_loc
          "unsupported expression in generic refinement term"
  in
  translate (Some expected_sort) expression

let surface_refined_type ~loc ~generics expression =
  let open Generic_refinement in
  let fields = surface_record ~loc expression in
  let base = string_constant (surface_required ~loc fields "base") in
  let sort_expression = surface_required ~loc fields "sort" in
  let index_sort =
    generic_sort_of_string ~loc:sort_expression.pexp_loc
      (string_constant sort_expression)
  in
  let index_expression = surface_required ~loc fields "index" in
  let predicate_expression = surface_required ~loc fields "predicate" in
  Refined
    {
      base;
      index_sort;
      index =
        generic_term_of_string ~loc:index_expression.pexp_loc ~generics
          ~expected_sort:index_sort
          (string_constant index_expression);
      predicate =
        generic_term_of_string ~loc:predicate_expression.pexp_loc ~generics
          ~expected_sort:(Base Bool)
          (string_constant predicate_expression);
    }

let surface_type_tuple ~loc ~generics expression =
  match expression.Parsetree.pexp_desc with
  | Pexp_tuple [ base; sort; index; predicate ] ->
      let record =
        Ast_helper.Exp.record
          [
            (Location.mknoloc (Longident.Lident "base"), base);
            (Location.mknoloc (Longident.Lident "sort"), sort);
            (Location.mknoloc (Longident.Lident "index"), index);
            (Location.mknoloc (Longident.Lident "predicate"), predicate);
          ]
          None
      in
      surface_refined_type ~loc ~generics record
  | _ ->
      typed_error ~loc
        "refinement parameters/results use (base, sort, index, predicate) \
         tuples"

let generic_scheme_of_attribute attribute =
  let open Generic_refinement in
  let mode =
    match attribute.Parsetree.attr_name.txt with
    | "refined.hindley" -> Some Hindley
    | "refined.horn" -> Some Horn
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
          ] -> (
          let generics_expression =
            surface_required ~loc:attribute.attr_loc fields "generics"
          in
          let generics =
            surface_list generics_expression
            |> List.map (fun expression ->
                match expression.pexp_desc with
                | Pexp_tuple [ name; sort ] ->
                    let name = string_constant name in
                    {
                      name;
                      mode;
                      sort =
                        generic_sort_of_string ~loc:sort.pexp_loc
                          (string_constant sort);
                    }
                | _ ->
                    typed_error ~loc:expression.pexp_loc
                      "generic declarations use (name, sort) tuples")
          in
          let generic_names = List.map (fun generic -> generic.name) generics in
          let parameters =
            surface_required ~loc:attribute.attr_loc fields "parameters"
            |> surface_list
            |> List.map (fun expression ->
                surface_type_tuple ~loc:expression.pexp_loc
                  ~generics:generic_names expression)
          in
          let result_expression =
            surface_required ~loc:attribute.attr_loc fields "result"
          in
          let result =
            surface_type_tuple ~loc:result_expression.pexp_loc
              ~generics:generic_names result_expression
          in
          let function_type =
            List.fold_right
              (fun input output -> Function (input, output))
              parameters result
          in
          let scheme =
            List.fold_right
              (fun generic scheme -> Forall (generic, scheme))
              generics (Mono function_type)
          in
          match well_formed scheme with
          | Ok () -> Some scheme
          | Error error ->
              let message =
                match error with
                | Ill_sorted message | Type_mismatch message -> message
                | Ill_formed_hindley generic ->
                    "Hindley generic `" ^ generic ^ "` is not value-dependent"
                | Ill_formed_horn generic ->
                    "Horn generic `" ^ generic ^ "` is not positive"
                | Arity_mismatch -> "generic scheme arity mismatch"
                | Unsolved_hindley generic ->
                    "unsolved Hindley generic `" ^ generic ^ "`"
                | Unsolved_horn generic ->
                    "unsolved Horn generic `" ^ generic ^ "`"
                | Unsupported_horn_constraint generic ->
                    "unsupported Horn constraint for `" ^ generic ^ "`"
                | Horn_fixpoint_did_not_converge iterations ->
                    Printf.sprintf
                      "Horn fixpoint did not converge in %d iterations"
                      iterations
                | Cyclic_instantiation evar ->
                    "cyclic generic instantiation `" ^ evar ^ "`"
              in
              typed_error ~loc:attribute.attr_loc
                "ill-formed generic refinement scheme: %s" message)
      | _ ->
          typed_error ~loc:attribute.attr_loc
            "expected [@@refined.hindley { generics; parameters; result }]")

let expression_refinement attributes =
  let refinements =
    List.filter
      (fun attribute -> attribute.attr_name.txt = "refined.type")
      attributes
  in
  match refinements with
  | [] -> None
  | [ attribute ] -> (
      match attribute.attr_payload with
      | PStr [ { pstr_desc = Pstr_eval (expression, _); _ } ] ->
          Some
            (surface_refined_type ~loc:attribute.attr_loc ~generics:[]
               expression)
      | _ ->
          typed_error ~loc:attribute.attr_loc
            "expected [@refined.type { base; sort; index; predicate }]")
  | attribute :: _ ->
      typed_error ~loc:attribute.attr_loc
        "an expression can have only one [@refined.type]"

let rec typed_expression registry (expression : Typedtree.expression) =
  let open Typed_core in
  let make desc =
    {
      desc;
      sort = typed_sort_of_type expression.exp_type;
      refinement = expression_refinement expression.exp_attributes;
      loc = span_of_location expression.exp_loc;
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
          Some
            Typed_core.
              { mode; pre; post; loc = span_of_location attribute.attr_loc })
    attributes

let typed_normalize expression =
  let open Typed_core in
  let counter = ref 0 in
  let fresh sort refinement loc =
    let index = !counter in
    incr counter;
    let symbol =
      { key = "refined_anf_" ^ string_of_int index; display = "_anf" }
    in
    (symbol, { desc = Var symbol; sort; refinement; loc })
  in
  let rec atoms expressions continuation =
    match expressions with
    | [] -> continuation []
    | expression :: rest ->
        anf expression (fun atom ->
            atoms rest (fun atoms -> continuation (atom :: atoms)))
  and bind_operation original desc continuation =
    let operation = { original with desc } in
    let symbol, variable =
      fresh original.sort original.refinement original.loc
    in
    let body = continuation variable in
    {
      desc = Let (symbol, operation, body);
      sort = body.sort;
      refinement = body.refinement;
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
              refinement = body.refinement;
              loc = expression.loc;
            })
    | If (condition, if_true, if_false) ->
        anf condition (fun condition ->
            let if_true = anf if_true continuation in
            let if_false = anf if_false continuation in
            {
              desc = If (condition, if_true, if_false);
              sort = if_true.sort;
              refinement = expression.refinement;
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
              refinement = expression.refinement;
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
              loc = span_of_location attribute.attr_loc;
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

let register_generic_scheme registry scope ~name ~loc attributes =
  let schemes = List.filter_map generic_scheme_of_attribute attributes in
  match schemes with
  | [] -> ()
  | [ scheme ] ->
      let full_name = qualified_name scope name in
      Hashtbl.replace registry.Typed_core.generic_schemes_by_name full_name
        scheme;
      if not (Hashtbl.mem registry.generic_schemes_by_name name) then
        Hashtbl.add registry.generic_schemes_by_name name scheme
  | _ ->
      typed_error ~loc
        "a function can export only one generic refinement scheme"

let register_generic_binding registry scope binding =
  match binding.Typedtree.vb_pat.pat_desc with
  | Typedtree.Tpat_var (_, name, _) ->
      register_generic_scheme registry scope ~name:name.txt ~loc:binding.vb_loc
        binding.vb_attributes
  | _ -> ()

let register_generic_value registry scope
    (description : Typedtree.value_description) =
  register_generic_scheme registry scope ~name:description.val_name.txt
    ~loc:description.val_loc description.val_attributes

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
            List.iter (register_logic_symbol registry scope) bindings;
            List.iter (register_generic_binding registry scope) bindings
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
            register_logic_value registry scope description;
            register_generic_value registry scope description
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
  generic_schemes : (string * Generic_refinement.scheme) list;
  axioms : Typed_core.axiom list;
}

let current_rmi_version = 2

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
  ensure_supported_version ();
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
  let generic_schemes =
    let prefix = cmt.cmt_modname ^ "." in
    Hashtbl.fold
      (fun name scheme entries ->
        if String.starts_with ~prefix name then (name, scheme) :: entries
        else entries)
      registry.generic_schemes_by_name []
  in
  let rmi =
    {
      format_version = current_rmi_version;
      ocaml_version = Sys.ocaml_version;
      unit_name = cmt.cmt_modname;
      interface_digest = Option.map Digest.to_hex cmt.cmt_interface_digest;
      logic_symbols;
      generic_schemes;
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
  List.iter
    (fun (name, scheme) ->
      Hashtbl.replace registry.Typed_core.generic_schemes_by_name name scheme;
      let short =
        match List.rev (String.split_on_char '.' name) with
        | short :: _ -> short
        | [] -> name
      in
      if not (Hashtbl.mem registry.generic_schemes_by_name short) then
        Hashtbl.add registry.generic_schemes_by_name short scheme)
    rmi.generic_schemes;
  registry.axioms <- List.rev_append rmi.axioms registry.axioms

let program_of_cmt ~theories filename =
  ensure_supported_version ();
  let cmt = Cmt_format.read_cmt filename in
  match cmt.cmt_annots with
  | Cmt_format.Implementation structure ->
      let registry = new_typed_registry () in
      List.iter (load_rmi_into registry cmt) theories;
      typed_program_of_structure ~registry structure
  | Cmt_format.Interface _ ->
      typed_error ~loc:Location.none
        "expected a typed implementation .cmt, but received an interface"
  | Packed _ | Partial_implementation _ | Partial_interface _ ->
      typed_error ~loc:Location.none
        "expected a complete typed implementation .cmt; OCaml emitted only a \
         partial tree"
