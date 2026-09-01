open Refined_ir
open Refined_common
open Parsetree
open Asttypes
open Ocaml_5_5_attributes
open Ocaml_5_5_lowering

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
      S_tuple
        (List.map
           (function
             | None, element -> logic_sort_of_core_type registry scope element
             | Some _, element ->
                 typed_error ~loc:element.ptyp_loc
                   "labelled tuples are not supported in theory sorts")
           elements)
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
        Some { pexp_desc = Pexp_tuple [ (None, head); (None, tail) ]; _ } ) ->
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
              | Pexp_tuple [ (None, name); (None, sort) ] ->
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
