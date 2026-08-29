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
      abstract_sorts_by_name = Hashtbl.create 16;
      module_aliases = Hashtbl.create 16;
      functor_theories = Hashtbl.create 8;
      generic_schemes_by_name = Hashtbl.create 16;
      axioms = [];
      lemmas = [];
      checked_lemmas = [];
      proof_artifacts = [];
      datatype_templates = [];
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
    let owner_symbol =
      symbol_of_ident ~display:declaration.typ_name.txt declaration.typ_id
    in
    let parameters =
      List.map
        (fun (parameter, _) -> typed_sort_of_type parameter.Typedtree.ctyp_type)
        declaration.Typedtree.typ_params
    in
    let owner = S_app (owner_symbol, parameters) in
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
                  result = owner;
                }
              in
              typed_register_constructor registry constructor
                typed_constructor.cd_uid typed_constructor.cd_name.txt;
              constructor)
            declarations
        in
        registry.datatype_templates <-
          { owner; constructors } :: registry.datatype_templates
    | Ttype_record labels ->
        let arguments =
          List.map
            (fun label -> typed_sort_of_type label.Typedtree.ld_type.ctyp_type)
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
            result = owner;
          }
        in
        List.iteri
          (fun index (label : Typedtree.label_declaration) ->
            Hashtbl.replace registry.fields_by_uid (uid_key label.ld_uid)
              (constructor, index);
            Hashtbl.replace registry.fields_by_name label.ld_name.txt
              (constructor, index))
          labels;
        registry.datatype_templates <-
          { owner; constructors = [ constructor ] }
          :: registry.datatype_templates
    | Ttype_abstract | Ttype_open -> ()
  in
  visit_structure structure

let typed_lookup_constructor registry ~loc
    (description : Types.constructor_description) =
  match
    Hashtbl.find_opt registry.Typed_core.constructors_by_uid
      (uid_key description.cstr_uid)
  with
  | Some constructor ->
      {
        constructor with
        arguments = List.map typed_sort_of_type description.cstr_args;
        result = typed_sort_of_type description.cstr_res;
      }
  | None ->
      typed_error ~loc "constructor `%s` is outside the supported datatype set"
        description.cstr_name

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
        typed_lookup_constructor registry ~loc:pattern.pat_loc description
      in
      let patterns = List.map (typed_pattern registry) patterns in
      Pat_construct
        ( {
            constructor with
            arguments =
              List.map
                (fun (pattern : Typedtree.pattern) ->
                  typed_sort_of_type pattern.pat_type)
                (match pattern.pat_desc with
                | Tpat_construct (_, _, patterns, _) -> patterns
                | _ -> assert false);
            result = typed_sort_of_type pattern.pat_type;
          },
          patterns )
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

let typed_field registry ~loc (description : Types.label_description) =
  match
    Hashtbl.find_opt registry.Typed_core.fields_by_uid
      (uid_key description.Types.lbl_uid)
  with
  | Some (constructor, index) ->
      ( {
          constructor with
          arguments =
            Array.to_list description.lbl_all
            |> List.map (fun label -> typed_sort_of_type label.Types.lbl_arg);
          result = typed_sort_of_type description.lbl_res;
        },
        index )
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

let rec normalize_registered_sort registry sort =
  let open Typed_core in
  match sort with
  | S_app (symbol, arguments) -> (
      let arguments = List.map (normalize_registered_sort registry) arguments in
      match
        Hashtbl.find_opt registry.Typed_core.abstract_sorts_by_name symbol.key
      with
      | Some (S_app (abstract, _)) -> S_app (abstract, arguments)
      | _ -> S_app (symbol, arguments))
  | S_tuple sorts ->
      S_tuple (List.map (normalize_registered_sort registry) sorts)
  | (S_int | S_bool | S_unit | S_var _) as sort -> sort

let rec typed_expression registry (expression : Typedtree.expression) =
  let open Typed_core in
  let make desc =
    {
      desc;
      sort =
        typed_sort_of_type expression.exp_type
        |> normalize_registered_sort registry;
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
      let arguments = List.map recurse arguments in
      let constructor =
        typed_lookup_constructor registry ~loc:expression.exp_loc description
      in
      make
        (Construct
           ( {
               constructor with
               arguments = List.map (fun argument -> argument.sort) arguments;
               result = typed_sort_of_type expression.exp_type;
             },
             arguments ))
  | Texp_tuple expressions -> make (Tuple (List.map recurse expressions))
  | Texp_apply
      ( { exp_desc = Texp_ident (path, _, _); _ },
        [
          ( Nolabel,
            Some { exp_desc = Texp_construct (_, exception_, payloads); _ } );
        ] )
    when match List.rev (String.split_on_char '.' (Path.name path)) with
         | "raise" :: _ -> true
         | _ -> false -> (
      match exception_.Types.cstr_tag with
      | Cstr_extension _ ->
          let payload =
            match payloads with
            | [] -> None
            | [ payload ] -> Some (recurse payload)
            | _ ->
                typed_error ~loc:expression.exp_loc
                  "exception payload requires at most one argument"
          in
          make
            (Raise
               ( symbol_of_uid ~name:exception_.cstr_name exception_.cstr_uid,
                 payload ))
      | _ ->
          typed_error ~loc:expression.exp_loc
            "raise currently requires a nullary exception constructor")
  | Texp_apply
      ( { exp_desc = Texp_ident (path, _, _); _ },
        [
          ( Nolabel,
            Some { exp_desc = Texp_construct (_, operation, payloads); _ } );
        ] )
    when match List.rev (String.split_on_char '.' (Path.name path)) with
         | "perform" :: _ -> true
         | _ -> false -> (
      match operation.Types.cstr_tag with
      | Cstr_extension _ ->
          let payload =
            match payloads with
            | [] -> None
            | [ payload ] -> Some (recurse payload)
            | _ ->
                typed_error ~loc:expression.exp_loc
                  "effect payload requires at most one argument"
          in
          make
            (Perform
               ( symbol_of_uid ~name:operation.cstr_name operation.cstr_uid,
                 payload ))
      | _ ->
          typed_error ~loc:expression.exp_loc
            "Effect.perform currently requires a nullary effect operation")
  | Texp_apply
      ( { exp_desc = Texp_ident (path, _, _); _ },
        [
          (Nolabel, Some thunk);
          (Nolabel, Some _argument);
          (Nolabel, Some handler);
        ] )
    when match List.rev (String.split_on_char '.' (Path.name path)) with
         | "match_with" :: _ -> true
         | _ -> false ->
      let thunk_body =
        match thunk.exp_desc with
        | Texp_function (_, Tfunction_body body) -> body
        | _ ->
            typed_error ~loc:thunk.exp_loc
              "Effect.Deep.match_with requires an inline thunk"
      in
      let fields =
        match handler.exp_desc with
        | Texp_record { fields; extended_expression = None; _ } -> fields
        | _ ->
            typed_error ~loc:handler.exp_loc
              "Effect.Deep.match_with requires a literal handler record"
      in
      let field name =
        Array.to_list fields
        |> List.find_map (fun (description, definition) ->
            if description.Types.lbl_name <> name then None
            else
              match definition with
              | Typedtree.Overridden (_, value) -> Some value
              | Kept _ -> None)
      in
      (match field "retc" with
      | Some
          {
            exp_desc =
              Texp_function
                ( [
                    {
                      fp_kind =
                        Tparam_pat { pat_desc = Tpat_var (parameter, _, _); _ };
                      _;
                    };
                  ],
                  Tfunction_body { exp_desc = Texp_ident (result, _, _); _ } );
            _;
          }
        when Path.same result (Path.Pident parameter) ->
          ()
      | _ ->
          typed_error ~loc:handler.exp_loc
            "effect handler retc must be the identity function");
      (match field "exnc" with
      | Some { exp_desc = Texp_ident (path, _, _); _ }
        when match List.rev (String.split_on_char '.' (Path.name path)) with
             | "raise" :: _ -> true
             | _ -> false ->
          ()
      | _ ->
          typed_error ~loc:handler.exp_loc
            "effect handler exnc must propagate with raise");
      let effc =
        match field "effc" with
        | Some { exp_desc = Texp_function (_, Tfunction_body body); _ } -> body
        | _ ->
            typed_error ~loc:handler.exp_loc
              "effect handler requires an inline effc function"
      in
      let handlers =
        match effc.exp_desc with
        | Texp_match (_, cases, [], Total) ->
            List.filter_map
              (fun (case : Typedtree.computation Typedtree.case) ->
                let pattern =
                  value_pattern_of_computation ~loc:case.c_lhs.pat_loc
                    case.c_lhs
                in
                match (pattern.pat_desc, case.c_rhs.exp_desc) with
                | ( Tpat_construct (_, operation, payload_patterns, _),
                    Texp_construct
                      ( _,
                        _,
                        [
                          {
                            exp_desc =
                              Texp_function (_, Tfunction_body handler_body);
                            _;
                          };
                        ] ) ) -> (
                    match operation.Types.cstr_tag with
                    | Cstr_extension _ ->
                        let payload_binder =
                          match payload_patterns with
                          | [] -> None
                          | [ { pat_desc = Tpat_var (ident, name, _); _ } ] ->
                              Some (symbol_of_ident ~display:name.txt ident)
                          | _ ->
                              typed_error ~loc:pattern.pat_loc
                                "effect payload handler requires a variable"
                        in
                        let rec handler_action expression =
                          match expression.Typedtree.exp_desc with
                          | Texp_apply
                              ( { exp_desc = Texp_ident (path, _, _); _ },
                                [
                                  (Nolabel, Some _continuation);
                                  (Nolabel, Some value);
                                ] )
                            when match
                                   List.rev
                                     (String.split_on_char '.' (Path.name path))
                                 with
                                 | "continue" :: _ -> true
                                 | _ -> false ->
                              Resume (recurse value)
                          | Texp_ifthenelse (condition, if_true, Some if_false)
                            ->
                              Conditional
                                ( recurse condition,
                                  handler_action if_true,
                                  handler_action if_false )
                          | _ -> Abort (recurse expression)
                        in
                        let action = handler_action handler_body in
                        Some
                          ( symbol_of_uid ~name:operation.cstr_name
                              operation.cstr_uid,
                            payload_binder,
                            action )
                    | _ -> None)
                | Tpat_any, Texp_construct (_, _, []) -> None
                | _ ->
                    typed_error ~loc:case.c_rhs.exp_loc
                      "unsupported effect handler clause")
              cases
        | _ ->
            typed_error ~loc:effc.exp_loc
              "effect handler effc must match on the operation"
      in
      make (Handle (recurse thunk_body, handlers))
  | Texp_apply
      ( { exp_desc = Texp_ident (path, _, _); _ },
        [ (Nolabel, Some { exp_desc = Texp_ident (cell, _, _); _ }) ] )
    when match List.rev (String.split_on_char '.' (Path.name path)) with
         | "!" :: _ -> true
         | _ -> false ->
      make (Deref (symbol_of_path cell))
  | Texp_apply
      ( { exp_desc = Texp_ident (path, _, _); _ },
        [
          (Nolabel, Some { exp_desc = Texp_ident (cell, _, _); _ });
          (Nolabel, Some value);
        ] )
    when match List.rev (String.split_on_char '.' (Path.name path)) with
         | ":=" :: _ -> true
         | _ -> false ->
      make (Assign (symbol_of_path cell, recurse value))
  | Texp_apply
      ({ exp_desc = Texp_ident (path, _, _); _ }, [ (Nolabel, Some initial) ])
    when match List.rev (String.split_on_char '.' (Path.name path)) with
         | "ref" :: _ -> true
         | _ -> false ->
      make (Ref (typed_sort_of_type initial.exp_type, recurse initial))
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
  | Texp_let
      ( Nonrecursive,
        [
          {
            vb_pat = { pat_desc = Tpat_var (ident, name, _); _ };
            vb_expr =
              {
                exp_desc =
                  Texp_apply
                    ( { exp_desc = Texp_ident (path, _, _); _ },
                      [ (Nolabel, Some initial) ] );
                _;
              };
            _;
          };
        ],
        body )
    when match List.rev (String.split_on_char '.' (Path.name path)) with
         | "ref" :: _ -> true
         | _ -> false ->
      make
        (Let_ref
           ( symbol_of_ident ~display:name.txt ident,
             typed_sort_of_type initial.exp_type,
             recurse initial,
             recurse body ))
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
  | Texp_sequence (first, second) ->
      make (Sequence (recurse first, recurse second))
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
  | Texp_try (body, cases, []) ->
      let exception_pattern (pattern : Typedtree.pattern) =
        match pattern.pat_desc with
        | Tpat_any -> Exn_any
        | Tpat_construct (_, description, payload_patterns, _) -> (
            match description.Types.cstr_tag with
            | Cstr_extension _ ->
                let payload_binder =
                  match payload_patterns with
                  | [] -> None
                  | [ { pat_desc = Tpat_var (ident, name, _); _ } ] ->
                      Some (symbol_of_ident ~display:name.txt ident)
                  | _ ->
                      typed_error ~loc:pattern.pat_loc
                        "exception payload handler requires a variable"
                in
                Exn
                  ( symbol_of_uid ~name:description.cstr_name
                      description.cstr_uid,
                    payload_binder )
            | _ ->
                typed_error ~loc:pattern.pat_loc
                  "exception handler pattern is not an exception")
        | _ ->
            typed_error ~loc:pattern.pat_loc
              "exception handlers currently require nullary exception or _"
      in
      let cases =
        List.map
          (fun (case : Typedtree.value Typedtree.case) ->
            if Option.is_some case.c_guard then
              typed_error ~loc:case.c_rhs.exp_loc
                "guarded exception handlers are not supported";
            (exception_pattern case.c_lhs, recurse case.c_rhs))
          cases
      in
      make (Try (recurse body, cases))
  | Texp_try (_, _, _ :: _) ->
      typed_error ~loc:expression.exp_loc
        "effect handlers are not yet lowered to relational Core"
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
      make
        (Record
           ( {
               constructor with
               arguments = List.map (fun value -> value.sort) values;
               result = typed_sort_of_type expression.exp_type;
             },
             values ))
  | Texp_field (record, _, description) ->
      let constructor, index =
        typed_field registry ~loc:expression.exp_loc description
      in
      make
        (Field
           ( { constructor with result = typed_sort_of_type record.exp_type },
             index,
             recurse record ))
  | _ ->
      typed_error ~loc:expression.exp_loc
        "unsupported Typedtree expression in the MVP Core"

let contract_ghost_sort registry ~loc text =
  let open Typed_core in
  let rec convert core_type =
    match core_type.Parsetree.ptyp_desc with
    | Ptyp_constr ({ txt; _ }, arguments) -> (
        let name = longident_name txt in
        let short = String.split_on_char '.' name |> List.rev |> List.hd in
        let arguments = List.map convert arguments in
        match (name, arguments) with
        | "int", [] -> Typed_core.S_int
        | "bool", [] -> S_bool
        | "unit", [] -> S_unit
        | "list", [ argument ] ->
            S_app ({ key = "list"; display = "list" }, [ argument ])
        | "option", [ argument ] ->
            S_app ({ key = "option"; display = "option" }, [ argument ])
        | _ -> (
            let abstract =
              match
                Hashtbl.find_opt registry.Typed_core.abstract_sorts_by_name name
              with
              | Some sort -> Some sort
              | None -> Hashtbl.find_opt registry.abstract_sorts_by_name short
            in
            match abstract with
            | Some (S_app (symbol, parameters))
              when List.length parameters = List.length arguments ->
                S_app (symbol, arguments)
            | Some sort when arguments = [] -> sort
            | Some _ ->
                typed_error ~loc
                  "ghost sort `%s` has the wrong number of parameters" text
            | None -> (
                let candidates =
                  registry.datatype_templates
                  |> List.filter_map (fun (datatype : Typed_core.datatype) ->
                      match datatype.owner with
                      | S_app (symbol, parameters)
                        when symbol.display = short
                             && List.length parameters = List.length arguments
                        ->
                          Some (S_app (symbol, arguments))
                      | _ -> None)
                  |> List.sort_uniq compare
                in
                match candidates with
                | [ sort ] -> sort
                | [] -> typed_error ~loc "unknown ghost sort `%s`" text
                | _ -> typed_error ~loc "ambiguous ghost sort `%s`" text)))
    | Ptyp_tuple elements -> S_tuple (List.map convert elements)
    | _ -> typed_error ~loc "unsupported ghost sort `%s`" text
  in
  let lexbuf = Lexing.from_string text in
  Location.init lexbuf loc.Location.loc_start.pos_fname;
  try convert (Parse.core_type lexbuf) with
  | Location.Error _ as error -> raise error
  | _ -> typed_error ~loc "cannot parse ghost sort `%s`" text

let typed_contracts registry attributes =
  List.filter_map
    (fun attribute ->
      match contract_of_attribute attribute with
      | None -> None
      | Some
          ( mode,
            pre,
            post,
            result_state,
            result_fresh,
            witnesses,
            witness_relation,
            ghosts,
            raises,
            state,
            modifies,
            requires_state,
            state_witnesses,
            performs,
            outcomes,
            outcome_state,
            outcome_modifies ) ->
          Some
            Typed_core.
              {
                mode;
                pre;
                post;
                result_state;
                result_fresh;
                witnesses;
                witness_relation;
                ghosts =
                  List.map
                    (fun (name, sort) ->
                      ( name,
                        contract_ghost_sort registry ~loc:attribute.attr_loc
                          sort ))
                    ghosts;
                raises;
                state;
                modifies;
                requires_state;
                state_witnesses;
                performs;
                outcomes =
                  List.map
                    (fun (kind, name, post, witnesses, witness_relation) ->
                      Typed_core.
                        { kind; name; post; witnesses; witness_relation })
                    outcomes;
                outcome_state;
                outcome_modifies;
                loc = span_of_location attribute.attr_loc;
              })
    attributes

let typed_measure attributes arguments =
  let measures =
    List.filter_map
      (fun attribute ->
        if attribute.Parsetree.attr_name.txt <> "refined.measure" then None
        else
          match attribute.attr_payload with
          | PStr [ { pstr_desc = Pstr_eval (expression, _); _ } ] ->
              Some (attribute, string_constant expression)
          | _ ->
              typed_error ~loc:attribute.attr_loc
                "expected [@refined.measure \"integer_parameter\"]")
      attributes
  in
  match measures with
  | [] -> None
  | [ (attribute, name) ] -> (
      match
        List.find_opt
          (fun ((symbol : Typed_core.symbol), _) -> symbol.display = name)
          arguments
      with
      | Some (symbol, Typed_core.S_int) -> Some symbol
      | Some _ ->
          typed_error ~loc:attribute.attr_loc
            "termination measure `%s` must name an int parameter" name
      | None ->
          typed_error ~loc:attribute.attr_loc
            "termination measure `%s` is not a function parameter" name)
  | (attribute, _) :: _ ->
      typed_error ~loc:attribute.attr_loc
        "a function can have only one termination measure"

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
    | Raise (exception_, payload) ->
        let payload = Option.map (fun payload -> anf payload Fun.id) payload in
        { expression with desc = Raise (exception_, payload) }
    | Perform (operation, None) ->
        bind_operation expression (Perform (operation, None)) continuation
    | Perform (operation, Some payload) ->
        anf payload (fun payload ->
            bind_operation expression
              (Perform (operation, Some payload))
              continuation)
    | Handle (body, handlers) ->
        let body = anf body Fun.id in
        let handlers =
          let rec anf_action = function
            | Abort handler -> Abort (anf handler Fun.id)
            | Resume value -> Resume (anf value Fun.id)
            | Conditional (condition, if_true, if_false) ->
                Conditional
                  (anf condition Fun.id, anf_action if_true, anf_action if_false)
          in
          List.map
            (fun (operation, payload, action) ->
              (operation, payload, anf_action action))
            handlers
        in
        bind_operation expression (Handle (body, handlers)) continuation
    | Let_ref (symbol, sort, initial, body) ->
        let initial = anf initial Fun.id in
        let body = anf body Fun.id in
        bind_operation expression
          (Let_ref (symbol, sort, initial, body))
          continuation
    | Ref (sort, initial) ->
        anf initial (fun initial ->
            bind_operation expression (Ref (sort, initial)) continuation)
    | Deref symbol -> bind_operation expression (Deref symbol) continuation
    | Assign (symbol, value) ->
        anf value (fun value ->
            bind_operation expression (Assign (symbol, value)) continuation)
    | Sequence (first, second) ->
        let first = anf first Fun.id in
        let second = anf second Fun.id in
        bind_operation expression (Sequence (first, second)) continuation
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
    | Try (body, cases) ->
        let body = anf body Fun.id in
        let cases =
          List.map (fun (pattern, body) -> (pattern, anf body Fun.id)) cases
        in
        bind_operation expression (Try (body, cases)) continuation
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
        bind_operation expression
          (Choose
             (List.map (fun expression -> anf expression Fun.id) expressions))
          continuation
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
  let contracts = typed_contracts registry binding.Typedtree.vb_attributes in
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
        |> List.map (fun (symbol, sort) ->
            (symbol, normalize_registered_sort registry sort))
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
          result =
            typed_sort_of_type body.exp_type
            |> normalize_registered_sort registry;
          body = typed_normalize (typed_expression registry body);
          contracts;
          measure = typed_measure binding.vb_attributes arguments;
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

let lookup_abstract_sort registry scope name =
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
      Hashtbl.find_opt registry.Typed_core.abstract_sorts_by_name candidate)
    names

let rec logic_sort_of_core_type registry scope core_type =
  let open Typed_core in
  match core_type.Parsetree.ptyp_desc with
  | Ptyp_constr ({ txt; _ }, arguments) -> (
      let name = longident_name txt in
      let arguments =
        List.map (logic_sort_of_core_type registry scope) arguments
      in
      match (name, arguments) with
      | "int", [] -> S_int
      | "bool", [] -> S_bool
      | "unit", [] -> S_unit
      | "list", [ argument ] ->
          S_app ({ key = "list"; display = "list" }, [ argument ])
      | "option", [ argument ] ->
          S_app ({ key = "option"; display = "option" }, [ argument ])
      | _ -> (
          match lookup_abstract_sort registry scope name with
          | Some (S_app (symbol, parameters))
            when List.length parameters = List.length arguments ->
              S_app (symbol, arguments)
          | Some _ ->
              typed_error ~loc:core_type.ptyp_loc
                "abstract sort `%s` has the wrong number of parameters" name
          | None -> S_app ({ key = name; display = name }, arguments)))
  | Ptyp_var name -> S_var ("a_" ^ smt_identifier name)
  | Ptyp_tuple elements ->
      S_tuple (List.map (logic_sort_of_core_type registry scope) elements)
  | _ -> typed_error ~loc:core_type.ptyp_loc "unsupported sort in theory axiom"

let logic_sort_of_string registry scope ~loc text =
  let lexbuf = Lexing.from_string text in
  Location.init lexbuf loc.Location.loc_start.pos_fname;
  try logic_sort_of_core_type registry scope (Parse.core_type lexbuf)
  with _ -> typed_error ~loc "cannot parse logical sort `%s`" text

let rec expression_list expression =
  match expression.Parsetree.pexp_desc with
  | Pexp_construct ({ txt = Lident "[]"; _ }, None) -> []
  | Pexp_construct
      ( { txt = Lident "::"; _ },
        Some { pexp_desc = Pexp_tuple [ head; tail ]; _ } ) ->
      head :: expression_list tail
  | _ -> typed_error ~loc:expression.pexp_loc "expected an OCaml list literal"

let theory_statement_of_attribute ~attribute_name ~kind registry scope attribute
    =
  if not (attribute_named attribute_name attribute) then None
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
              typed_error ~loc:attribute.attr_loc "%s is missing field `%s`"
                kind name
        in
        let name = string_constant (required "name") in
        let body = string_constant (required "body") in
        let variables =
          expression_list (required "vars")
          |> List.map (fun expression ->
              match expression.pexp_desc with
              | Pexp_tuple [ name; sort ] ->
                  ( string_constant name,
                    logic_sort_of_string registry scope ~loc:sort.pexp_loc
                      (string_constant sort) )
              | _ ->
                  typed_error ~loc:expression.pexp_loc
                    "%s vars must contain (name, sort) string pairs" kind)
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
          "expected [@@@%s { name; vars; body }]" attribute_name

let axiom_of_attribute =
  theory_statement_of_attribute ~attribute_name:"refined.axiom" ~kind:"axiom"

let lemma_of_attribute =
  theory_statement_of_attribute ~attribute_name:"refined.lemma" ~kind:"lemma"

let rec normalize_abstract_sort registry scope sort =
  let open Typed_core in
  match sort with
  | S_app (symbol, arguments) -> (
      let arguments =
        List.map (normalize_abstract_sort registry scope) arguments
      in
      match
        match Hashtbl.find_opt registry.abstract_sorts_by_name symbol.key with
        | Some sort -> Some sort
        | None -> lookup_abstract_sort registry scope symbol.display
      with
      | Some (S_app (abstract, parameters))
        when List.length parameters = List.length arguments ->
          S_app (abstract, arguments)
      | _ -> S_app (symbol, arguments))
  | S_tuple sorts ->
      S_tuple (List.map (normalize_abstract_sort registry scope) sorts)
  | (S_int | S_bool | S_unit | S_var _) as sort -> sort

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
    let arguments =
      List.map (normalize_abstract_sort registry scope) arguments
    in
    let result = normalize_abstract_sort registry scope result in
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
    let arguments =
      List.map (normalize_abstract_sort registry scope) arguments
    in
    let result = normalize_abstract_sort registry scope result in
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

let register_abstract_sort registry scope ~symbol declaration =
  if
    declaration.Typedtree.typ_kind = Typedtree.Ttype_abstract
    && Option.is_none declaration.typ_manifest
  then (
    let parameters =
      List.map
        (fun (parameter, _) -> typed_sort_of_type parameter.Typedtree.ctyp_type)
        declaration.typ_params
    in
    let sort = Typed_core.S_app (symbol, parameters) in
    let name = declaration.typ_name.txt in
    let full_name = qualified_name scope name in
    Hashtbl.replace registry.Typed_core.abstract_sorts_by_name full_name sort;
    if not (Hashtbl.mem registry.abstract_sorts_by_name name) then
      Hashtbl.add registry.abstract_sorts_by_name name sort)

let register_module_alias registry scope name target =
  let full_name = qualified_name scope name in
  Hashtbl.replace registry.Typed_core.module_aliases full_name target;
  if not (Hashtbl.mem registry.module_aliases name) then
    Hashtbl.add registry.module_aliases name target

let instantiate_functor_theory registry scope name functor_name argument =
  let open Typed_core in
  let theory =
    match
      Hashtbl.find_opt registry.Typed_core.functor_theories functor_name
    with
    | Some theory -> theory
    | None ->
        typed_error ~loc:Location.none
          "module functor `%s` has no refinement theory transformer"
          functor_name
  in
  let target = qualified_name scope name in
  let application_identity =
    if theory.generative then target
    else theory.functor_name ^ "(" ^ argument ^ ")"
  in
  let replace_prefix prefix replacement value =
    if value = prefix then replacement
    else if String.starts_with ~prefix:(prefix ^ ".") value then
      replacement
      ^ String.sub value (String.length prefix)
          (String.length value - String.length prefix)
    else value
  in
  let rec map_sort = function
    | Typed_core.S_app (symbol, arguments) ->
        let arguments = List.map map_sort arguments in
        let key = symbol.key in
        let short_parameter = theory.parameter_name in
        if
          theory.parameter_name <> ""
          && (key = theory.parameter_prefix
             || String.starts_with ~prefix:(theory.parameter_prefix ^ ".") key
             || key = short_parameter
             || String.starts_with ~prefix:(short_parameter ^ ".") key)
        then
          let actual =
            if
              key = short_parameter
              || String.starts_with ~prefix:(short_parameter ^ ".") key
            then replace_prefix short_parameter argument key
            else replace_prefix theory.parameter_prefix argument key
          in
          match Hashtbl.find_opt registry.abstract_sorts_by_name actual with
          | Some sort -> sort
          | None -> S_app ({ symbol with key = actual }, arguments)
        else
          let key =
            replace_prefix theory.result_prefix application_identity key
          in
          S_app ({ symbol with key }, arguments)
    | S_tuple sorts -> S_tuple (List.map map_sort sorts)
    | (S_int | S_bool | S_unit | S_var _) as sort -> sort
  in
  if theory.parameter_name <> "" then
    Hashtbl.replace registry.module_aliases
      (target ^ "." ^ theory.parameter_name)
      argument;
  List.iter
    (fun (key, sort) ->
      if
        not
          (key = theory.parameter_prefix
          || String.starts_with ~prefix:(theory.parameter_prefix ^ ".") key)
      then
        let key = replace_prefix theory.result_prefix target key in
        Hashtbl.replace registry.abstract_sorts_by_name key (map_sort sort))
    theory.abstract_sorts;
  List.iter
    (fun (key, symbol) ->
      let key = replace_prefix theory.result_prefix target key in
      let logic_name =
        {
          symbol.Typed_core.logic_name with
          key =
            replace_prefix
              ("logic." ^ theory.result_prefix)
              ("logic." ^ target) symbol.logic_name.key;
        }
      in
      let symbol =
        Typed_core.
          {
            logic_name;
            arguments = List.map map_sort symbol.arguments;
            result = map_sort symbol.result;
          }
      in
      Hashtbl.replace registry.logic_by_name key symbol)
    theory.logic_symbols;
  List.iter
    (fun (axiom : Typed_core.axiom) ->
      let axiom_name =
        replace_prefix theory.result_prefix target axiom.axiom_name
      in
      registry.axioms <-
        {
          axiom with
          axiom_name;
          scope = scope @ [ name ];
          variables =
            List.map (fun (name, sort) -> (name, map_sort sort)) axiom.variables;
        }
        :: registry.axioms)
    theory.axioms

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
              (axiom_of_attribute registry scope attribute);
            if attribute_named "refined.lemma" attribute then
              typed_error ~loc:attribute.attr_loc
                "checked lemmas must be declared in a module signature"
        | Tstr_type (_, declarations) ->
            List.iter
              (fun (declaration : Typedtree.type_declaration) ->
                register_abstract_sort registry scope
                  ~symbol:
                    (symbol_of_ident ~display:declaration.typ_name.txt
                       declaration.typ_id)
                  declaration)
              declarations
        | Tstr_module binding ->
            let nested =
              match binding.mb_name.txt with
              | Some name -> scope @ [ name ]
              | None -> scope
            in
            (match (binding.mb_name.txt, binding.mb_expr.mod_desc) with
            | Some name, Tmod_ident (_, target) ->
                let target = longident_name target.txt in
                let target =
                  if String.contains target '.' then target
                  else qualified_name scope target
                in
                register_module_alias registry scope name target
            | ( Some name,
                Tmod_apply
                  ( { mod_desc = Tmod_ident (_, functor_name); _ },
                    { mod_desc = Tmod_ident (_, argument); _ },
                    _ ) ) ->
                instantiate_functor_theory registry scope name
                  (longident_name functor_name.txt)
                  (longident_name argument.txt)
            | ( Some name,
                Tmod_apply
                  ( { mod_desc = Tmod_ident (_, functor_name); _ },
                    { mod_desc = Tmod_structure { str_items = []; _ }; _ },
                    _ ) ) ->
                instantiate_functor_theory registry scope name
                  (longident_name functor_name.txt)
                  ""
            | ( Some name,
                Tmod_apply_unit { mod_desc = Tmod_ident (_, functor_name); _ } )
              ->
                instantiate_functor_theory registry scope name
                  (longident_name functor_name.txt)
                  ""
            | _ -> ());
            Option.iter (visit nested) (module_structure binding.mb_expr)
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
        | Tsig_type (_, declarations) ->
            List.iter
              (fun (declaration : Typedtree.type_declaration) ->
                let name = declaration.Typedtree.typ_name.txt in
                register_abstract_sort registry scope
                  ~symbol:
                    Typed_core.
                      { key = qualified_name scope name; display = name }
                  declaration)
              declarations
        | Tsig_attribute attribute ->
            Option.iter
              (fun axiom ->
                registry.Typed_core.axioms <-
                  axiom :: registry.Typed_core.axioms)
              (axiom_of_attribute registry scope attribute);
            Option.iter
              (fun lemma ->
                registry.Typed_core.lemmas <- lemma :: registry.lemmas)
              (lemma_of_attribute registry scope attribute)
        | Tsig_module declaration -> (
            let nested =
              match declaration.md_name.txt with
              | Some name -> scope @ [ name ]
              | None -> scope
            in
            match (declaration.md_name.txt, declaration.md_type.mty_desc) with
            | Some name, Tmty_functor (Unit, result_type) ->
                let result_prefix = qualified_name scope name in
                let lemmas_before = registry.Typed_core.lemmas in
                visit_module_type nested result_type;
                if registry.lemmas != lemmas_before then
                  typed_error ~loc:declaration.md_loc
                    "checked lemmas in functor results are not supported";
                let starts key =
                  key = result_prefix
                  || String.starts_with ~prefix:(result_prefix ^ ".") key
                in
                let abstract_sorts =
                  Hashtbl.fold
                    (fun key sort result ->
                      if starts key then (key, sort) :: result else result)
                    registry.abstract_sorts_by_name []
                in
                let logic_symbols =
                  Hashtbl.fold
                    (fun key symbol result ->
                      if starts key then (key, symbol) :: result else result)
                    registry.logic_by_name []
                in
                let axioms =
                  List.filter
                    (fun (axiom : Typed_core.axiom) -> starts axiom.axiom_name)
                    registry.axioms
                  |> List.rev
                in
                Hashtbl.replace registry.functor_theories result_prefix
                  Typed_core.
                    {
                      functor_name = result_prefix;
                      generative = true;
                      parameter_name = "";
                      parameter_prefix = "";
                      result_prefix;
                      abstract_sorts;
                      logic_symbols;
                      axioms;
                      module_aliases = [];
                    }
            | ( Some name,
                Tmty_functor
                  (Named (Some parameter, _, parameter_type), result_type) ) ->
                let result_prefix = qualified_name scope name in
                let parameter_name = Ident.name parameter in
                let parameter_prefix = qualified_name nested parameter_name in
                visit_module_type (nested @ [ parameter_name ]) parameter_type;
                let lemmas_before = registry.Typed_core.lemmas in
                visit_module_type nested result_type;
                if registry.lemmas != lemmas_before then
                  typed_error ~loc:declaration.md_loc
                    "checked lemmas in functor results are not supported";
                let starts prefix name =
                  name = prefix
                  || String.starts_with ~prefix:(prefix ^ ".") name
                in
                let abstract_sorts =
                  Hashtbl.fold
                    (fun key sort result ->
                      if starts result_prefix key then (key, sort) :: result
                      else result)
                    registry.abstract_sorts_by_name []
                in
                let logic_symbols =
                  Hashtbl.fold
                    (fun key symbol result ->
                      if
                        starts result_prefix key
                        && not (starts parameter_prefix key)
                      then (key, symbol) :: result
                      else result)
                    registry.logic_by_name []
                in
                let axioms =
                  List.filter
                    (fun (axiom : Typed_core.axiom) ->
                      starts result_prefix axiom.axiom_name
                      && not (starts parameter_prefix axiom.axiom_name))
                    registry.axioms
                  |> List.rev
                in
                let module_aliases =
                  Hashtbl.fold
                    (fun key target result ->
                      if starts result_prefix key then (key, target) :: result
                      else result)
                    registry.module_aliases []
                in
                let theory =
                  Typed_core.
                    {
                      functor_name = result_prefix;
                      generative = false;
                      parameter_name;
                      parameter_prefix;
                      result_prefix;
                      abstract_sorts;
                      logic_symbols;
                      axioms;
                      module_aliases;
                    }
                in
                Hashtbl.replace registry.functor_theories result_prefix theory
            | Some name, Tmty_alias (_, target) ->
                let target = longident_name target.txt in
                let target =
                  if String.contains target '.' then target
                  else qualified_name scope target
                in
                register_module_alias registry scope name target
            | _ -> visit_module_type nested declaration.md_type)
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
  abstract_sorts : (string * Typed_core.sort) list;
  module_aliases : (string * string) list;
  functor_theories : (string * Typed_core.functor_theory) list;
  generic_schemes : (string * Generic_refinement.scheme) list;
  axioms : Typed_core.axiom list;
  checked_lemmas : Typed_core.axiom list;
  proof_artifacts : Refined_types.proof_artifact list;
}

let current_rmi_version = 5

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
  let lemma_names =
    List.map
      (fun (lemma : Typed_core.axiom) -> lemma.axiom_name)
      rmi.checked_lemmas
  in
  let artifact_names =
    List.map
      (fun (artifact : Refined_types.proof_artifact) -> artifact.lemma_name)
      rmi.proof_artifacts
  in
  if lemma_names <> artifact_names then
    typed_error ~loc:Location.none
      ".rmi `%s` has inconsistent checked-lemma artifacts" path;
  let trusted_axioms =
    List.map (fun (axiom : Typed_core.axiom) -> axiom.axiom_name) rmi.axioms
  in
  let rec validate_artifacts checked = function
    | [] -> ()
    | (artifact : Refined_types.proof_artifact) :: rest ->
        let subset members available =
          List.for_all (fun member -> List.mem member available) members
        in
        if
          (not (subset artifact.trusted_axioms trusted_axioms))
          || (not (subset artifact.checked_dependencies checked))
          || artifact.vc_digest = "" || artifact.solver = ""
          || artifact.timeout_seconds <= 0
        then
          typed_error ~loc:Location.none
            ".rmi `%s` has malformed verification metadata for lemma `%s`" path
            artifact.lemma_name;
        validate_artifacts (checked @ [ artifact.lemma_name ]) rest
  in
  validate_artifacts [] rmi.proof_artifacts;
  rmi

let write_rmi ~verify ~cmti ~output =
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
  let hidden_by_functor name =
    Hashtbl.fold
      (fun _ (theory : Typed_core.functor_theory) hidden ->
        hidden
        || name = theory.result_prefix
        || String.starts_with ~prefix:(theory.result_prefix ^ ".") name)
      registry.functor_theories false
  in
  let logic_symbols =
    Hashtbl.fold
      (fun name (logic_symbol : Typed_core.logic_symbol) entries ->
        if
          logic_symbol.logic_name.key = "logic." ^ name
          && (not (hidden_by_functor name))
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
        if String.starts_with ~prefix name && not (hidden_by_functor name) then
          (name, scheme) :: entries
        else entries)
      registry.generic_schemes_by_name []
  in
  let prefix = cmt.cmt_modname ^ "." in
  let abstract_sorts =
    Hashtbl.fold
      (fun name sort entries ->
        if String.starts_with ~prefix name && not (hidden_by_functor name) then
          (name, sort) :: entries
        else entries)
      registry.abstract_sorts_by_name []
  in
  let module_aliases =
    Hashtbl.fold
      (fun name target entries ->
        if String.starts_with ~prefix name && not (hidden_by_functor name) then
          (name, target) :: entries
        else entries)
      registry.module_aliases []
  in
  let functor_theories =
    Hashtbl.fold
      (fun name theory entries ->
        if String.starts_with ~prefix name then (name, theory) :: entries
        else entries)
      registry.functor_theories []
  in
  let checked_lemmas = List.rev registry.lemmas in
  let proof_artifacts = verify registry checked_lemmas in
  let artifact_names =
    List.map
      (fun (artifact : Refined_types.proof_artifact) -> artifact.lemma_name)
      proof_artifacts
  in
  let lemma_names =
    List.map (fun (lemma : Typed_core.axiom) -> lemma.axiom_name) checked_lemmas
  in
  let statement_names =
    lemma_names
    @ List.map
        (fun (axiom : Typed_core.axiom) -> axiom.axiom_name)
        (List.rev registry.axioms)
  in
  if
    List.length statement_names
    <> List.length (List.sort_uniq String.compare statement_names)
  then
    typed_error ~loc:Location.none
      "theory `%s` exports duplicate axiom/lemma names" cmt.cmt_modname;
  if artifact_names <> lemma_names then
    typed_error ~loc:Location.none
      "internal error: lemma verification artifacts do not match declarations";
  let rmi =
    {
      format_version = current_rmi_version;
      ocaml_version = Sys.ocaml_version;
      unit_name = cmt.cmt_modname;
      interface_digest = Option.map Digest.to_hex cmt.cmt_interface_digest;
      logic_symbols;
      abstract_sorts;
      module_aliases;
      generic_schemes;
      axioms =
        List.rev registry.axioms
        |> List.filter (fun (axiom : Typed_core.axiom) ->
            not (hidden_by_functor axiom.axiom_name));
      checked_lemmas;
      proof_artifacts;
      functor_theories;
    }
  in
  let temporary =
    Filename.temp_file ~temp_dir:(Filename.dirname output)
      (Filename.basename output ^ ".")
      ".tmp"
  in
  match
    let channel = open_out_bin temporary in
    Fun.protect
      ~finally:(fun () -> close_out channel)
      (fun () -> Marshal.to_channel channel rmi [])
  with
  | () -> Sys.rename temporary output
  | exception exception_ ->
      (try Sys.remove temporary with Sys_error _ -> ());
      raise exception_

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
    (fun (name, sort) ->
      Hashtbl.replace registry.Typed_core.abstract_sorts_by_name name sort;
      let short =
        match List.rev (String.split_on_char '.' name) with
        | short :: _ -> short
        | [] -> name
      in
      if not (Hashtbl.mem registry.abstract_sorts_by_name short) then
        Hashtbl.add registry.abstract_sorts_by_name short sort)
    rmi.abstract_sorts;
  List.iter
    (fun (name, target) ->
      Hashtbl.replace registry.Typed_core.module_aliases name target;
      let short =
        match List.rev (String.split_on_char '.' name) with
        | short :: _ -> short
        | [] -> name
      in
      if not (Hashtbl.mem registry.module_aliases short) then
        Hashtbl.add registry.module_aliases short target)
    rmi.module_aliases;
  List.iter
    (fun (name, theory) ->
      Hashtbl.replace registry.Typed_core.functor_theories name theory)
    rmi.functor_theories;
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
  registry.axioms <- List.rev_append rmi.axioms registry.axioms;
  registry.checked_lemmas <-
    List.rev_append rmi.checked_lemmas registry.checked_lemmas;
  registry.proof_artifacts <-
    List.rev_append rmi.proof_artifacts registry.proof_artifacts

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
