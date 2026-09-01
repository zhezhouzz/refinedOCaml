open Refined_ir
open Refined_common
open Parsetree
open Asttypes

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
        Some { pexp_desc = Pexp_tuple [ (None, head); (None, tail) ]; _ } ) ->
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
  | Pexp_tuple [ (None, base); (None, sort); (None, index); (None, predicate) ]
    ->
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
                | Pexp_tuple [ (None, name); (None, sort) ] ->
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
