open Refined_ir
open Refined_common
open Parsetree
open Asttypes
open Ocaml_5_5_attributes

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
      let display = Path.last path in
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
  | Types.Tconstr (path, arguments, _)
    when (Path.name path = "ref"
         || String.ends_with ~suffix:".ref" (Path.name path))
         && List.length arguments = 1 ->
      S_app
        ({ key = "ref"; display = "ref" }, List.map typed_sort_of_type arguments)
  | Types.Tconstr (path, arguments, _) ->
      S_app (symbol_of_path path, List.map typed_sort_of_type arguments)
  | Types.Ttuple elements ->
      S_tuple
        (List.map
           (function
             | None, element -> typed_sort_of_type element
             | Some _, _ ->
                 typed_error ~loc:Location.none
                   "labelled tuple types are not supported by the 5.5 frontend")
           elements)
  | Types.Tvar name | Types.Tunivar name ->
      let suffix =
        match name with
        | Some name -> smt_identifier name
        | None -> string_of_int (Types.get_id type_expr)
      in
      S_var ("a_" ^ suffix)
  | Types.Tpoly (body, _) -> typed_sort_of_type body
  | Types.Tlink body -> typed_sort_of_type body
  | Types.Tarrow (Nolabel, domain, codomain, _) ->
      S_arrow (typed_sort_of_type domain, typed_sort_of_type codomain)
  | Types.Tarrow _ ->
      typed_error ~loc:Location.none
        "labelled arrows are not supported by the refinement frontend"
  | Types.Tfunctor _ ->
      typed_error ~loc:Location.none
        "functor values are not part of the logical sort language"
  | Types.Tobject _ | Types.Tfield _ | Types.Tnil | Types.Tsubst _
  | Types.Tvariant _ | Types.Tpackage _ ->
      typed_error ~loc:Location.none
        "unsupported OCaml type in the MVP logical sort language"

let new_typed_registry () =
  let registry =
    Typed_core.
      {
        constructors_by_uid = Hashtbl.create 32;
        constructors_by_name = Hashtbl.create 32;
        fields_by_uid = Hashtbl.create 32;
        fields_by_name = Hashtbl.create 32;
        logic_by_name = Hashtbl.create 32;
        abstract_sorts_by_name = Hashtbl.create 16;
        concrete_sorts_by_name = Hashtbl.create 16;
        choose_symbols = Hashtbl.create 8;
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
  in
  let parameter = Typed_core.S_var "predef_a" in
  let unit =
    Typed_core.
      {
        symbol = { key = "predef.unit"; display = "()" };
        arguments = [];
        result = S_unit;
      }
  in
  let list_owner =
    Typed_core.S_app ({ key = "list"; display = "list" }, [ parameter ])
  in
  let nil =
    Typed_core.
      {
        symbol = { key = "predef.list.nil"; display = "[]" };
        arguments = [];
        result = list_owner;
      }
  in
  let cons =
    Typed_core.
      {
        symbol = { key = "predef.list.cons"; display = "::" };
        arguments = [ parameter; list_owner ];
        result = list_owner;
      }
  in
  let option_owner =
    Typed_core.S_app ({ key = "option"; display = "option" }, [ parameter ])
  in
  let none =
    Typed_core.
      {
        symbol = { key = "predef.option.none"; display = "None" };
        arguments = [];
        result = option_owner;
      }
  in
  let some =
    Typed_core.
      {
        symbol = { key = "predef.option.some"; display = "Some" };
        arguments = [ parameter ];
        result = option_owner;
      }
  in
  List.iter
    (fun (constructor : Typed_core.constructor) ->
      Hashtbl.add registry.constructors_by_name constructor.symbol.display
        constructor)
    [ unit; nil; cons; none; some ];
  registry.datatype_templates <-
    [
      Typed_core.
        { owner = list_owner; constructors = [ nil; cons ]; native_smt = true };
      Typed_core.
        {
          owner = option_owner;
          constructors = [ none; some ];
          native_smt = true;
        };
    ];
  registry

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
  let rec visit_structure scope structure =
    List.iter
      (fun item ->
        match item.Typedtree.str_desc with
        | Typedtree.Tstr_type (_, declarations) ->
            List.iter (register scope) declarations
        | Tstr_module binding ->
            Option.iter
              (fun name ->
                Option.iter
                  (visit_structure (scope @ [ name ]))
                  (module_structure binding.mb_expr))
              binding.mb_name.txt
        | Tstr_recmodule bindings ->
            List.iter
              (fun (binding : Typedtree.module_binding) ->
                Option.iter
                  (fun name ->
                    Option.iter
                      (visit_structure (scope @ [ name ]))
                      (module_structure binding.mb_expr))
                  binding.mb_name.txt)
              bindings
        | _ -> ())
      structure.Typedtree.str_items
  and register scope declaration =
    let native_smt =
      List.exists
        (fun attribute ->
          attribute.Parsetree.attr_name.txt = "refined.native_datatype")
        declaration.Typedtree.typ_attributes
    in
    let owner_symbol =
      symbol_of_ident ~display:declaration.typ_name.txt declaration.typ_id
    in
    let parameters =
      List.map
        (fun (parameter, _) -> typed_sort_of_type parameter.Typedtree.ctyp_type)
        declaration.Typedtree.typ_params
    in
    let owner = S_app (owner_symbol, parameters) in
    let qualified = qualified_name scope declaration.typ_name.txt in
    Hashtbl.replace registry.concrete_sorts_by_name qualified owner;
    if
      not (Hashtbl.mem registry.concrete_sorts_by_name declaration.typ_name.txt)
    then
      Hashtbl.add registry.concrete_sorts_by_name declaration.typ_name.txt owner;
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
          { owner; constructors; native_smt } :: registry.datatype_templates
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
          { owner; constructors = [ constructor ]; native_smt }
          :: registry.datatype_templates
    | Ttype_abstract | Ttype_open -> ()
    | Ttype_external _ ->
        typed_error ~loc:declaration.typ_loc
          "external type declarations are not supported by the 5.5 frontend"
  in
  visit_structure [] structure

let typed_lookup_constructor registry ~loc
    (description : Data_types.constructor_description) =
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
  | None -> (
      match
        Hashtbl.find_opt registry.Typed_core.constructors_by_name
          description.cstr_name
      with
      | Some constructor ->
          let constructor =
            {
              constructor with
              arguments = List.map typed_sort_of_type description.cstr_args;
              result = typed_sort_of_type description.cstr_res;
            }
          in
          Hashtbl.replace registry.constructors_by_uid
            (uid_key description.cstr_uid)
            constructor;
          constructor
      | None ->
          typed_error ~loc
            "constructor `%s` is outside the supported datatype set"
            description.cstr_name)

let rec typed_pattern registry (pattern : Typedtree.pattern) =
  let open Typed_core in
  match pattern.pat_desc with
  | Typedtree.Tpat_any -> Pat_any
  | Tpat_var (ident, name, _) ->
      Pat_var (symbol_of_ident ~display:name.txt ident)
  | Tpat_alias (inner, ident, name, _, _) ->
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
          List.map
            (function
              | None, pattern -> typed_pattern registry pattern
              | Some _, pattern ->
                  typed_error ~loc:pattern.pat_loc
                    "labelled tuple patterns are not supported by the 5.5 \
                     frontend")
            patterns )
  | _ -> typed_error ~loc:pattern.pat_loc "unsupported pattern in the MVP Core"

let value_pattern_of_computation ~loc pattern =
  match pattern.Typedtree.pat_desc with
  | Typedtree.Tpat_value value -> (value :> Typedtree.pattern)
  | _ ->
      typed_error ~loc "exception/effect patterns are not part of the MVP Core"

let typed_field registry ~loc (description : Data_types.label_description) =
  match
    Hashtbl.find_opt registry.Typed_core.fields_by_uid
      (uid_key description.Data_types.lbl_uid)
  with
  | Some (constructor, index) ->
      ( {
          constructor with
          arguments =
            Array.to_list description.lbl_all
            |> List.map (fun label ->
                typed_sort_of_type label.Data_types.lbl_arg);
          result = typed_sort_of_type description.lbl_res;
        },
        index )
  | None ->
      typed_error ~loc "record field `%s` is outside the supported datatype set"
        description.lbl_name

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
  | S_arrow (domain, codomain) ->
      S_arrow
        ( normalize_registered_sort registry domain,
          normalize_registered_sort registry codomain )
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
  let application_arguments ~loc arguments =
    List.map
      (function
        | Asttypes.Nolabel, Typedtree.Arg argument -> recurse argument
        | _, Typedtree.Arg _ ->
            typed_error ~loc
              "labelled applications are not part of the MVP Core"
        | _, Typedtree.Omitted () ->
            typed_error ~loc
              "partial labelled applications are not part of the MVP Core")
      arguments
  in
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
  | Texp_tuple expressions ->
      make
        (Tuple
           (List.map
              (function
                | None, expression -> recurse expression
                | Some _, expression ->
                    typed_error ~loc:expression.exp_loc
                      "labelled tuple expressions are not supported by the 5.5 \
                       frontend")
              expressions))
  | Texp_apply
      ( { exp_desc = Texp_ident (path, _, _); _ },
        [
          ( Nolabel,
            Typedtree.Arg
              { exp_desc = Texp_construct (_, exception_, payloads); _ } );
        ] )
    when match List.rev (String.split_on_char '.' (Path.name path)) with
         | "raise" :: _ -> true
         | _ -> false -> (
      match exception_.Data_types.cstr_tag with
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
            Typedtree.Arg
              { exp_desc = Texp_construct (_, operation, payloads); _ } );
        ] )
    when match List.rev (String.split_on_char '.' (Path.name path)) with
         | "perform" :: _ -> true
         | _ -> false -> (
      match operation.Data_types.cstr_tag with
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
          (Nolabel, Typedtree.Arg thunk);
          (Nolabel, Typedtree.Arg _argument);
          (Nolabel, Typedtree.Arg handler);
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
            if description.Data_types.lbl_name <> name then None
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
                    match operation.Data_types.cstr_tag with
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
                                  (Nolabel, Typedtree.Arg _continuation);
                                  (Nolabel, Typedtree.Arg value);
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
        [ (Nolabel, Typedtree.Arg { exp_desc = Texp_ident (cell, _, _); _ }) ]
      )
    when match List.rev (String.split_on_char '.' (Path.name path)) with
         | "!" :: _ -> true
         | _ -> false ->
      make (Deref (symbol_of_path cell))
  | Texp_apply
      ( { exp_desc = Texp_ident (path, _, _); _ },
        [
          (Nolabel, Typedtree.Arg { exp_desc = Texp_ident (cell, _, _); _ });
          (Nolabel, Typedtree.Arg value);
        ] )
    when match List.rev (String.split_on_char '.' (Path.name path)) with
         | ":=" :: _ -> true
         | _ -> false ->
      make (Assign (symbol_of_path cell, recurse value))
  | Texp_apply
      ( { exp_desc = Texp_ident (path, _, _); _ },
        [ (Nolabel, Typedtree.Arg initial) ] )
    when match List.rev (String.split_on_char '.' (Path.name path)) with
         | "ref" :: _ -> true
         | _ -> false ->
      make (Ref (typed_sort_of_type initial.exp_type, recurse initial))
  | Texp_function (parameters, Tfunction_body body) ->
      let parameters =
        List.map
          (fun (parameter : Typedtree.function_param) ->
            match parameter.fp_kind with
            | Tparam_pat { pat_desc = Tpat_var (ident, name, _); pat_type; _ }
              ->
                ( symbol_of_ident ~display:name.txt ident,
                  typed_sort_of_type pat_type
                  |> normalize_registered_sort registry )
            | Tparam_pat
                {
                  pat_desc =
                    Tpat_alias ({ pat_desc = Tpat_any; _ }, ident, name, _, _);
                  pat_type;
                  _;
                } ->
                ( symbol_of_ident ~display:name.txt ident,
                  typed_sort_of_type pat_type
                  |> normalize_registered_sort registry )
            | _ ->
                typed_error ~loc:parameter.fp_loc
                  "anonymous function parameters must be simple variables")
          parameters
      in
      make (Lambda (parameters, recurse body))
  | Texp_apply (callee, raw_arguments) -> (
      let arguments =
        application_arguments ~loc:expression.exp_loc raw_arguments
      in
      let description =
        match callee.exp_desc with
        | Texp_ident (_, _, description) -> Some description
        | _ -> None
      in
      if
        (match callee.exp_desc with
          | Texp_ident (path, _, _) ->
              Hashtbl.mem registry.Typed_core.choose_symbols
                (symbol_of_path path).key
          | _ -> false)
        || Option.exists
             (fun description ->
               List.exists
                 (fun attribute ->
                   attribute.Parsetree.attr_name.txt = "refined.choose")
                 description.Types.val_attributes)
             description
      then make (Choose arguments)
      else
        match callee.exp_desc with
        | Texp_ident (path, _, _) ->
            make (Apply (symbol_of_path path, arguments))
        | _ -> make (Apply_value (recurse callee, arguments)))
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
                      [ (Nolabel, Typedtree.Arg initial) ] );
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
            match description.Data_types.cstr_tag with
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
        | "ref", [ argument ] ->
            S_app ({ key = "ref"; display = "ref" }, [ argument ])
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
    | Ptyp_tuple elements ->
        S_tuple
          (List.map
             (function
               | None, element -> convert element
               | Some _, element ->
                   typed_error ~loc:element.ptyp_loc
                     "labelled tuples are not supported in refinement sorts")
             elements)
    | Ptyp_var name -> S_var ("a_" ^ smt_identifier name)
    | _ -> typed_error ~loc "unsupported ghost sort `%s`" text
  in
  let lexbuf = Lexing.from_string text in
  Location.init lexbuf loc.Location.loc_start.pos_fname;
  try convert (Parse.core_type lexbuf) with
  | Location.Error _ as error -> raise error
  | _ -> typed_error ~loc "cannot parse ghost sort `%s`" text

let refined_base_of_surface registry ~loc ~expected_sort
    (base : surface_refined_base) =
  let base_sort = contract_ghost_sort registry ~loc base.surface_type in
  let base_sort = normalize_registered_sort registry base_sort in
  if base_sort <> expected_sort then
    typed_error ~loc "refined type `%s` does not match the inferred OCaml type"
      base.surface_type;
  Typed_core.
    {
      value_name = base.surface_value;
      base_sort;
      predicate = base.surface_predicate;
    }

let refined_type_of_surface registry ~loc ~arguments ~result surface =
  let check_predicate env (base : Typed_core.refined_base) =
    let formula =
      parse_formula ~filename:loc.Location.loc_start.pos_fname ~loc
        base.predicate
    in
    let allowed_variable name =
      name = base.value_name
      || List.exists (fun (bound, _) -> bound = name) env
      || Option.is_some (binary_operator name)
      || name = "not"
      || Hashtbl.fold
           (fun _ (symbol : Typed_core.logic_symbol) found ->
             found || symbol.logic_name.display = name)
           registry.Typed_core.logic_by_name false
    in
    let iterator =
      {
        Ast_iterator.default_iterator with
        expr =
          (fun self expression ->
            (match expression.Parsetree.pexp_desc with
            | Pexp_ident { txt = Lident name; _ }
              when not (allowed_variable name) ->
                typed_error ~loc:expression.pexp_loc
                  "refinement variable `%s` is not in Liquid scope" name
            | _ -> ());
            Ast_iterator.default_iterator.expr self expression);
      }
    in
    iterator.expr iterator formula
  in
  let rec convert env expected_sort expected_parameters = function
    | Surface_base base -> (
        match expected_sort with
        | Typed_core.S_arrow _ ->
            typed_error ~loc
              "refined function type has fewer arrows than the inferred OCaml \
               type"
        | _ ->
            let base =
              refined_base_of_surface registry ~loc ~expected_sort base
            in
            check_predicate env base;
            Typed_core.Refined_base base)
    | Surface_arrow (parameter, domain, codomain) -> (
        match expected_sort with
        | Typed_core.S_arrow (domain_sort, codomain_sort) ->
            (match expected_parameters with
            | (expected : Typed_core.symbol) :: _
              when parameter <> expected.display ->
                typed_error ~loc
                  "refined parameter `%s` does not match OCaml parameter `%s`"
                  parameter expected.display
            | _ -> ());
            let domain = convert env domain_sort [] domain in
            let expected_parameters =
              match expected_parameters with [] -> [] | _ :: rest -> rest
            in
            Typed_core.Refined_arrow
              {
                parameter;
                domain;
                codomain =
                  convert
                    ((parameter, (smt_identifier parameter, domain_sort)) :: env)
                    codomain_sort expected_parameters codomain;
              }
        | _ ->
            typed_error ~loc
              "refined function type has more arrows than the inferred OCaml \
               type")
  in
  let function_sort =
    List.fold_right
      (fun (_, argument_sort) result ->
        Typed_core.S_arrow (argument_sort, result))
      arguments result
  in
  convert [] function_sort (List.map fst arguments) surface

let typed_contracts registry ~arguments ~result attributes =
  List.filter_map
    (fun attribute ->
      match contract_of_attribute attribute with
      | None -> None
      | Some
          ( mode,
            surface_type,
            result_state,
            result_fresh,
            result_references,
            result_fresh_references,
            result_reference_permissions,
            result_recursive,
            result_region,
            requires_regions,
            consumes_regions,
            universals,
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
          List.iter
            (fun name ->
              if
                not
                  (List.exists
                     (fun ((symbol : Typed_core.symbol), _) ->
                       symbol.display = name)
                     arguments)
              then
                typed_error ~loc:attribute.attr_loc
                  "coverage universal `%s` is not a function parameter" name)
            universals;
          Some
            Typed_core.
              {
                mode;
                refined_type =
                  refined_type_of_surface registry ~loc:attribute.attr_loc
                    ~arguments ~result surface_type;
                function_arity = List.length arguments;
                result_state;
                result_fresh;
                result_references;
                result_fresh_references;
                result_reference_permissions;
                result_recursive;
                result_region;
                requires_regions;
                consumes_regions;
                universals;
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

let typed_measure registry attributes arguments =
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
                "expected [@refined.measure \"parameter[, parameter ...]\"]")
      attributes
  in
  match measures with
  | [] -> []
  | [ (attribute, text) ] ->
      let names =
        String.split_on_char ',' text
        |> List.map String.trim
        |> List.filter (fun name -> name <> "")
      in
      if names = [] then
        typed_error ~loc:attribute.attr_loc
          "termination measure must name at least one parameter";
      if List.length names <> List.length (List.sort_uniq String.compare names)
      then
        typed_error ~loc:attribute.attr_loc
          "termination measure parameters must be distinct";
      List.map
        (fun name ->
          match
            List.find_opt
              (fun ((symbol : Typed_core.symbol), _) -> symbol.display = name)
              arguments
          with
          | Some (symbol, Typed_core.S_int) -> symbol
          | Some (symbol, sort) ->
              let native_datatype =
                List.exists
                  (fun (datatype : Typed_core.datatype) ->
                    datatype.native_smt
                    &&
                    match (datatype.owner, sort) with
                    | ( Typed_core.S_app (owner, owner_arguments),
                        Typed_core.S_app (actual, actual_arguments) ) ->
                        owner.key = actual.key
                        && List.length owner_arguments
                           = List.length actual_arguments
                    | owner, actual -> owner = actual)
                  registry.Typed_core.datatype_templates
              in
              if native_datatype then symbol
              else
                typed_error ~loc:attribute.attr_loc
                  "termination measure `%s` must name an int parameter or a \
                   [@@refined.native_datatype] parameter"
                  name
          | None ->
              typed_error ~loc:attribute.attr_loc
                "termination measure `%s` is not a function parameter" name)
        names
  | (attribute, _) :: _ ->
      typed_error ~loc:attribute.attr_loc
        "a function can have only one termination measure"

let typed_normalize expression =
  let open Typed_core in
  let fresh sort refinement loc =
    let symbol = symbol_of_ident (Ident.create_local "_anf") in
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
    | Lambda (parameters, body) ->
        continuation
          { expression with desc = Lambda (parameters, anf body Fun.id) }
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
    | Apply_value (callee, expressions) ->
        anf callee (fun callee ->
            atoms expressions (fun expressions ->
                bind_operation expression
                  (Apply_value (callee, expressions))
                  continuation))
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
  | Tpat_alias ({ pat_desc = Tpat_any; _ }, ident, name, _, _) ->
      Some
        ( symbol_of_ident ~display:name.txt ident,
          typed_sort_of_type pattern.pat_type )
  | _ -> None

let typed_register_choices registry structure =
  let rec module_structure = function
    | { Typedtree.mod_desc = Typedtree.Tmod_structure structure; _ } ->
        Some structure
    | { mod_desc = Tmod_constraint (inner, _, _, _); _ } ->
        module_structure inner
    | _ -> None
  in
  let rec visit structure =
    List.iter
      (fun item ->
        match item.Typedtree.str_desc with
        | Typedtree.Tstr_value (_, bindings) ->
            List.iter
              (fun binding ->
                if
                  List.exists
                    (fun attribute ->
                      attribute.Parsetree.attr_name.txt = "refined.choose")
                    binding.Typedtree.vb_attributes
                then
                  match binding.vb_pat.pat_desc with
                  | Typedtree.Tpat_var (ident, name, _) ->
                      let symbol = symbol_of_ident ~display:name.txt ident in
                      Hashtbl.replace registry.Typed_core.choose_symbols
                        symbol.key ()
                  | _ ->
                      typed_error ~loc:binding.vb_pat.pat_loc
                        "a choice primitive binding must have a simple name")
              bindings
        | Tstr_module binding ->
            Option.iter visit (module_structure binding.mb_expr)
        | Tstr_recmodule bindings ->
            List.iter
              (fun (binding : Typedtree.module_binding) ->
                Option.iter visit (module_structure binding.mb_expr))
              bindings
        | _ -> ())
      structure.Typedtree.str_items
  in
  visit structure

let typed_function registry binding =
  let open Typed_core in
  let has_contract =
    List.exists
      (fun attribute ->
        match attribute.Parsetree.attr_name.txt with
        | "refined.over" | "refined.coverage" -> true
        | _ -> false)
      binding.Typedtree.vb_attributes
  in
  match binding.vb_expr.exp_desc with
  | Typedtree.Texp_function (parameters, Tfunction_body body) ->
      let symbol =
        match binding.vb_pat.pat_desc with
        | Typedtree.Tpat_var (ident, name, _) ->
            symbol_of_ident ~display:name.txt ident
        | _ ->
            if not has_contract then
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
      let result =
        typed_sort_of_type body.exp_type |> normalize_registered_sort registry
      in
      let contracts =
        typed_contracts registry ~arguments ~result
          binding.Typedtree.vb_attributes
      in
      Some
        {
          symbol;
          arguments;
          result;
          body = typed_normalize (typed_expression registry body);
          contracts;
          measure = typed_measure registry binding.vb_attributes arguments;
        }
  | _ ->
      if not has_contract then None
      else
        typed_error ~loc:binding.vb_expr.exp_loc
          "a refined binding must be an explicitly written function"
