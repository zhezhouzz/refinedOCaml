open Refined_ir
open Refined_types
open Refined_common
open Parsetree
open Asttypes

module Sort_term = struct
  type t = Typed_core.sort

  type head =
    | Integer
    | Boolean
    | Unit
    | Tuple
    | Application of Typed_core.symbol

  let view = function
    | Typed_core.S_var variable -> `Variable variable
    | S_int -> `Node (Integer, [])
    | S_bool -> `Node (Boolean, [])
    | S_unit -> `Node (Unit, [])
    | S_tuple elements -> `Node (Tuple, elements)
    | S_app (symbol, arguments) -> `Node (Application symbol, arguments)

  let make_node head children =
    match (head, children) with
    | Integer, [] -> Typed_core.S_int
    | Boolean, [] -> S_bool
    | Unit, [] -> S_unit
    | Tuple, elements -> S_tuple elements
    | Application symbol, arguments -> S_app (symbol, arguments)
    | (Integer | Boolean | Unit), _ -> invalid_arg "base sort with arguments"

  let equal_head left right =
    match (left, right) with
    | Integer, Integer | Boolean, Boolean | Unit, Unit | Tuple, Tuple -> true
    | Application left, Application right -> left.key = right.key
    | _ -> false

  let equal = ( = )
end

module Sort_evars = Evar_context.Make (Sort_term)

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
  "C_"
  ^ smt_identifier constructor.Typed_core.symbol.key
  ^ "__"
  ^ smt_identifier (typed_smt_sort constructor.result)

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
  let names = candidates scope in
  let rec expand_alias visited name =
    if List.mem name visited then name
    else
      let parts = String.split_on_char '.' name in
      let rec longest length =
        if length = 0 then None
        else
          let prefix =
            parts |> List.to_seq |> Seq.take length |> List.of_seq
            |> String.concat "."
          in
          match Hashtbl.find_opt registry.Typed_core.module_aliases prefix with
          | Some target ->
              let suffix =
                parts |> List.to_seq |> Seq.drop length |> List.of_seq
              in
              Some (String.concat "." (target :: suffix))
          | None -> longest (length - 1)
      in
      match longest (List.length parts - 1) with
      | None -> name
      | Some expanded -> expand_alias (name :: visited) expanded
  in
  List.find_map
    (fun candidate ->
      let expanded = expand_alias [] candidate in
      match Hashtbl.find_opt registry.Typed_core.logic_by_name expanded with
      | Some symbol -> Some symbol
      | None -> Hashtbl.find_opt registry.logic_by_name candidate)
    names

let typed_specialize_program (program : Typed_core.program)
    (function_def : Typed_core.function_def) pre_expression post_expression =
  let open Typed_core in
  let substitutions = Sort_evars.create () in
  let substitute = Sort_evars.substitute substitutions in
  let unify ~loc formal actual =
    match Sort_evars.unify substitutions ~formal ~actual with
    | Ok () -> ()
    | Error (Occurs (variable, actual)) ->
        typed_error ~loc "cyclic instantiation for `%s` in %s" variable
          (typed_smt_sort actual)
    | Error (Shape_mismatch (formal, actual)) ->
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
                program.registry.datatype_templates
            with
            | Some datatype -> datatype.owner
            | None ->
                typed_error ~loc:expression.pexp_loc
                  "constructor `%s` has no registered owner" name)
        | None ->
            typed_error ~loc:expression.pexp_loc "unknown constructor `%s`" name
        )
    | Pexp_apply
        ( { pexp_desc = Pexp_ident { txt = Lident "not"; _ }; _ },
          [ (Nolabel, argument) ] ) ->
        unify ~loc:expression.pexp_loc S_bool (recurse argument);
        S_bool
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
        | Some ("=" | "distinct") -> S_bool
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
              typed_error_at expression.loc
                "logical predicate `%s` has an unsupported application arity"
                symbol.display;
            List.iter2
              (fun formal (actual : Typed_core.expr) ->
                unify
                  ~loc:(location_of_span actual.Typed_core.loc)
                  formal actual.sort)
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
    | Var _ | Int _ | Bool _ | Raise _ | Deref _ -> ()
    | Try (body, cases) ->
        recurse body;
        List.iter (fun (_, handler) -> recurse handler) cases
    | Let_ref (_, _, initial, body) ->
        recurse initial;
        recurse body
    | Assign (_, value) -> recurse value
    | Sequence (first, second) ->
        recurse first;
        recurse second
  in
  ignore (infer_formula [] formula_env pre_expression);
  ignore
    (infer_formula []
       (("result", function_def.result) :: formula_env)
       post_expression);
  infer_core function_def.body;
  if not (Sort_evars.has_solutions substitutions) then program
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
    let specialize_statements statements =
      List.map
        (fun (axiom : Typed_core.axiom) ->
          {
            axiom with
            variables =
              List.map
                (fun (name, sort) -> (name, substitute sort))
                axiom.variables;
          })
        statements
    in
    let axioms = specialize_statements program.registry.axioms in
    let checked_lemmas =
      specialize_statements program.registry.checked_lemmas
    in
    let registry =
      { program.registry with logic_by_name; axioms; checked_lemmas }
    in
    { program with registry }

let typed_monomorphize_datatypes (program : Typed_core.program)
    (function_def : Typed_core.function_def) =
  let templates = program.registry.Typed_core.datatype_templates in
  let template_for = function
    | Typed_core.S_app (symbol, _) ->
        List.find_opt
          (fun (datatype : Typed_core.datatype) ->
            match datatype.owner with
            | S_app (owner, _) -> owner.key = symbol.key
            | _ -> false)
          templates
    | _ -> None
  in
  let rec closed = function
    | Typed_core.S_var _ -> false
    | S_tuple sorts | S_app (_, sorts) -> List.for_all closed sorts
    | S_int | S_bool | S_unit -> true
  in
  let instances = Hashtbl.create 16 in
  let open_instance = ref None in
  let rec collect sort =
    (match template_for sort with
    | Some _ when closed sort ->
        Hashtbl.replace instances (typed_smt_sort sort) sort
    | Some _ -> open_instance := Some sort
    | None -> ());
    match sort with
    | Typed_core.S_tuple sorts | S_app (_, sorts) -> List.iter collect sorts
    | S_int | S_bool | S_unit | S_var _ -> ()
  in
  let rec collect_pattern = function
    | Typed_core.Pat_construct (constructor, patterns) ->
        collect constructor.result;
        List.iter collect constructor.arguments;
        List.iter collect_pattern patterns
    | Pat_tuple (sort, patterns) ->
        collect sort;
        List.iter collect_pattern patterns
    | Pat_alias (pattern, _) -> collect_pattern pattern
    | Pat_any | Pat_var _ | Pat_int _ | Pat_bool _ -> ()
  in
  let rec collect_expression (expression : Typed_core.expr) =
    collect expression.sort;
    match expression.desc with
    | Var _ | Int _ | Bool _ | Raise _ | Deref _ -> ()
    | Construct (constructor, expressions) | Record (constructor, expressions)
      ->
        collect constructor.result;
        List.iter collect constructor.arguments;
        List.iter collect_expression expressions
    | Tuple expressions | Choose expressions | Apply (_, expressions) ->
        List.iter collect_expression expressions
    | If (condition, if_true, if_false) ->
        List.iter collect_expression [ condition; if_true; if_false ]
    | Let (_, value, body) -> List.iter collect_expression [ value; body ]
    | Match (scrutinee, cases) ->
        collect_expression scrutinee;
        List.iter
          (fun (pattern, body) ->
            collect_pattern pattern;
            collect_expression body)
          cases
    | Field (constructor, _, record) ->
        collect constructor.result;
        List.iter collect constructor.arguments;
        collect_expression record
    | Try (body, cases) ->
        collect_expression body;
        List.iter (fun (_, handler) -> collect_expression handler) cases
    | Let_ref (_, sort, initial, body) ->
        collect sort;
        collect_expression initial;
        collect_expression body
    | Assign (_, value) -> collect_expression value
    | Sequence (first, second) ->
        collect_expression first;
        collect_expression second
  in
  List.iter (fun (_, sort) -> collect sort) function_def.arguments;
  collect function_def.result;
  collect_expression function_def.body;
  (match !open_instance with
  | Some sort ->
      typed_error_at function_def.body.loc
        "parameterized ADT `%s` has no finite closed use-site instance"
        (typed_smt_sort sort)
  | None -> ());
  let instantiate (template : Typed_core.datatype) concrete =
    let substitutions = Sort_evars.create () in
    (match
       Sort_evars.unify substitutions ~formal:template.owner ~actual:concrete
     with
    | Ok () -> ()
    | Error _ -> assert false);
    let substitute = Sort_evars.substitute substitutions in
    {
      Typed_core.owner = concrete;
      constructors =
        List.map
          (fun (constructor : Typed_core.constructor) ->
            {
              constructor with
              arguments = List.map substitute constructor.arguments;
              result = substitute constructor.result;
            })
          template.constructors;
    }
  in
  let datatypes =
    Hashtbl.fold
      (fun _ concrete result ->
        match template_for concrete with
        | Some template -> instantiate template concrete :: result
        | None -> result)
      instances []
    |> List.sort (fun left right ->
        String.compare
          (typed_smt_sort left.Typed_core.owner)
          (typed_smt_sort right.Typed_core.owner))
  in
  let constructors_by_name = Hashtbl.create 32 in
  let constructors_by_uid = Hashtbl.create 32 in
  let constructor_candidates symbol_key =
    List.concat_map
      (fun (datatype : Typed_core.datatype) ->
        List.filter
          (fun (constructor : Typed_core.constructor) ->
            constructor.symbol.key = symbol_key)
          datatype.constructors)
      datatypes
  in
  Hashtbl.iter
    (fun name (template : Typed_core.constructor) ->
      match constructor_candidates template.symbol.key with
      | [ constructor ] -> Hashtbl.replace constructors_by_name name constructor
      | _ -> ())
    program.registry.constructors_by_name;
  Hashtbl.iter
    (fun uid (template : Typed_core.constructor) ->
      match constructor_candidates template.symbol.key with
      | [ constructor ] -> Hashtbl.replace constructors_by_uid uid constructor
      | _ -> ())
    program.registry.constructors_by_uid;
  let fields_by_name = Hashtbl.create 32 in
  let fields_by_uid = Hashtbl.create 32 in
  let specialize_field table key ((template : Typed_core.constructor), index) =
    match constructor_candidates template.Typed_core.symbol.key with
    | [ constructor ] -> Hashtbl.replace table key (constructor, index)
    | _ -> Hashtbl.replace table key (template, index)
  in
  Hashtbl.iter (specialize_field fields_by_name) program.registry.fields_by_name;
  Hashtbl.iter (specialize_field fields_by_uid) program.registry.fields_by_uid;
  let registry =
    {
      program.registry with
      constructors_by_uid;
      constructors_by_name;
      fields_by_uid;
      fields_by_name;
      datatypes;
    }
  in
  { program with registry }

exception Logic_needs_expected of Location.t * string

let elaborate_formula ?(scope = []) ?(expected = Typed_core.S_bool) registry env
    expression =
  let open Logic_term in
  let ensure_sort ~loc expected actual =
    if expected <> actual then
      typed_error ~loc "logical sort mismatch: expected %s but got %s"
        (typed_smt_sort expected) (typed_smt_sort actual)
  in
  let finish ?expected ~loc term =
    Option.iter (fun expected -> ensure_sort ~loc expected term.sort) expected;
    term
  in
  let constructors_named name =
    List.concat_map
      (fun (datatype : Typed_core.datatype) ->
        List.filter
          (fun (constructor : Typed_core.constructor) ->
            constructor.symbol.display = name)
          datatype.constructors)
      registry.Typed_core.datatypes
  in
  let constructor_arguments argument =
    match argument with
    | None -> []
    | Some { Parsetree.pexp_desc = Pexp_tuple expressions; _ } -> expressions
    | Some expression -> [ expression ]
  in
  let rec elaborate ?expected expression =
    let loc = expression.Parsetree.pexp_loc in
    match expression.pexp_desc with
    | Pexp_ident { txt; _ } -> (
        let name = longident_name txt in
        match List.assoc_opt name env with
        | Some (variable, sort) ->
            finish ?expected ~loc { desc = Variable variable; sort }
        | None -> (
            match typed_lookup_logic registry scope name with
            | Some logic_symbol when logic_symbol.arguments = [] ->
                finish ?expected ~loc
                  {
                    desc = Application (Logic logic_symbol, []);
                    sort = logic_symbol.result;
                  }
            | _ -> typed_error ~loc "unknown logical variable `%s`" name))
    | Pexp_constant { pconst_desc = Pconst_integer (value, _); _ } ->
        finish ?expected ~loc
          { desc = Integer (int_of_string value); sort = Typed_core.S_int }
    | Pexp_construct ({ txt = Lident "true"; _ }, None) ->
        finish ?expected ~loc { desc = Boolean true; sort = Typed_core.S_bool }
    | Pexp_construct ({ txt = Lident "false"; _ }, None) ->
        finish ?expected ~loc { desc = Boolean false; sort = Typed_core.S_bool }
    | Pexp_construct ({ txt; _ }, argument) ->
        let name = longident_last txt in
        let expressions = constructor_arguments argument in
        let candidates =
          constructors_named name
          |> List.filter (fun (constructor : Typed_core.constructor) ->
              List.length constructor.Typed_core.arguments
              = List.length expressions)
          |> List.filter (fun (constructor : Typed_core.constructor) ->
              match expected with
              | Some expected -> constructor.result = expected
              | None -> true)
        in
        let candidates =
          match (expected, candidates) with
          | Some _, _ | None, [] | None, [ _ ] -> candidates
          | None, candidates ->
              let inferred = List.map elaborate expressions in
              List.filter
                (fun (constructor : Typed_core.constructor) ->
                  List.map (fun term -> term.sort) inferred
                  = constructor.Typed_core.arguments)
                candidates
        in
        let constructor =
          match candidates with
          | [ constructor ] -> constructor
          | [] ->
              typed_error ~loc "constructor `%s` has no matching logic sort"
                name
          | _ ->
              raise (Logic_needs_expected (loc, "constructor `" ^ name ^ "`"))
        in
        let arguments =
          List.map2
            (fun expected expression -> elaborate ~expected expression)
            constructor.arguments expressions
        in
        finish ?expected ~loc
          {
            desc = Application (Constructor constructor, arguments);
            sort = constructor.result;
          }
    | Pexp_apply
        ( { pexp_desc = Pexp_ident { txt = Lident "not"; _ }; _ },
          [ (Nolabel, argument) ] ) ->
        let argument = elaborate ~expected:Typed_core.S_bool argument in
        finish ?expected ~loc
          {
            desc = Application (Builtin "not", [ argument ]);
            sort = Typed_core.S_bool;
          }
    | Pexp_apply ({ pexp_desc = Pexp_ident { txt; _ }; _ }, arguments) -> (
        let name = longident_name txt in
        let arguments =
          List.map
            (function
              | Nolabel, argument -> argument
              | _ -> typed_error ~loc "logical applications cannot use labels")
            arguments
        in
        match (binary_operator name, arguments) with
        | Some (("=" | "distinct") as operator), [ left; right ] ->
            let left, right =
              try
                let left = elaborate left in
                (left, elaborate ~expected:left.sort right)
              with Logic_needs_expected _ ->
                let right = elaborate right in
                (elaborate ~expected:right.sort left, right)
            in
            finish ?expected ~loc
              {
                desc = Application (Builtin operator, [ left; right ]);
                sort = Typed_core.S_bool;
              }
        | Some (("+" | "-" | "*" | "div" | "mod") as operator), [ left; right ]
          ->
            let left = elaborate ~expected:Typed_core.S_int left in
            let right = elaborate ~expected:Typed_core.S_int right in
            finish ?expected ~loc
              {
                desc = Application (Builtin operator, [ left; right ]);
                sort = Typed_core.S_int;
              }
        | Some (("<" | "<=" | ">" | ">=") as operator), [ left; right ] ->
            let left = elaborate ~expected:Typed_core.S_int left in
            let right = elaborate ~expected:Typed_core.S_int right in
            finish ?expected ~loc
              {
                desc = Application (Builtin operator, [ left; right ]);
                sort = Typed_core.S_bool;
              }
        | Some (("and" | "or" | "=>") as operator), [ left; right ] ->
            let left = elaborate ~expected:Typed_core.S_bool left in
            let right = elaborate ~expected:Typed_core.S_bool right in
            finish ?expected ~loc
              {
                desc = Application (Builtin operator, [ left; right ]);
                sort = Typed_core.S_bool;
              }
        | _ -> (
            match typed_lookup_logic registry scope name with
            | Some logic_symbol ->
                if List.length arguments <> List.length logic_symbol.arguments
                then
                  typed_error ~loc "logical predicate `%s` expects %d arguments"
                    name
                    (List.length logic_symbol.arguments);
                let arguments =
                  List.map2
                    (fun expected expression -> elaborate ~expected expression)
                    logic_symbol.arguments arguments
                in
                finish ?expected ~loc
                  {
                    desc = Application (Logic logic_symbol, arguments);
                    sort = logic_symbol.result;
                  }
            | None -> typed_error ~loc "unknown logical predicate `%s`" name))
    | Pexp_field (record, { txt; _ }) ->
        let name = longident_last txt in
        let record = elaborate record in
        let family, index =
          match Hashtbl.find_opt registry.Typed_core.fields_by_name name with
          | Some entry -> entry
          | None -> typed_error ~loc "unknown logical record field `%s`" name
        in
        let candidates =
          List.concat_map
            (fun (datatype : Typed_core.datatype) -> datatype.constructors)
            registry.datatypes
          |> List.filter (fun constructor ->
              let constructor : Typed_core.constructor = constructor in
              constructor.Typed_core.symbol.key = family.symbol.key
              && constructor.result = record.sort)
        in
        let constructor =
          match candidates with
          | [ constructor ] -> constructor
          | [] ->
              typed_error ~loc
                "record field `%s` does not belong to logic sort %s" name
                (typed_smt_sort record.sort)
          | _ -> typed_error ~loc "record field `%s` remains ambiguous" name
        in
        let sort = List.nth constructor.arguments index in
        finish ?expected ~loc
          {
            desc = Application (Selector (constructor, index), [ record ]);
            sort;
          }
    | _ -> typed_error ~loc "unsupported refinement formula"
  in
  try elaborate ~expected expression
  with Logic_needs_expected (loc, construct) ->
    typed_error ~loc "%s needs an expected logic sort" construct

let rec logic_term_smt (term : Logic_term.t) =
  let open Logic_term in
  match term.desc with
  | Variable variable -> variable
  | Integer value -> string_of_int value
  | Boolean value -> string_of_bool value
  | Application (head, arguments) ->
      let name =
        match head with
        | Builtin name -> name
        | Logic symbol -> typed_logic_name symbol
        | Constructor constructor -> typed_constructor_name constructor
        | Selector (constructor, index) -> typed_selector constructor index
      in
      let arguments = List.map logic_term_smt arguments in
      if arguments = [] then name else app name arguments

let typed_formula ?scope ?expected registry env expression =
  elaborate_formula ?scope ?expected registry env expression |> logic_term_smt

let formula_theory_symbols ?scope ?expected registry env expression =
  elaborate_formula ?scope ?expected registry env expression
  |> Logic_term.theory_symbols

let slice_program_theory (program : Typed_core.program) ~roots =
  let registry = program.registry in
  let artifacts_by_name = Hashtbl.create 16 in
  List.iter
    (fun (artifact : Refined_types.proof_artifact) ->
      Hashtbl.replace artifacts_by_name artifact.lemma_name artifact)
    registry.proof_artifacts;
  let statement kind (axiom : Typed_core.axiom) =
    let formula =
      parse_formula ~filename:axiom.loc.file
        ~loc:(location_of_span axiom.loc)
        axiom.body
    in
    let env =
      List.map
        (fun (name, sort) -> (name, (smt_identifier name, sort)))
        axiom.variables
    in
    let symbols =
      formula_theory_symbols ~scope:axiom.scope registry env formula
      |> List.sort_uniq String.compare
    in
    let requires =
      match kind with
      | `Axiom -> []
      | `Lemma -> (
          match Hashtbl.find_opt artifacts_by_name axiom.axiom_name with
          | Some artifact ->
              artifact.trusted_axioms @ artifact.checked_dependencies
          | None -> [])
    in
    Theory_slice.{ name = axiom.axiom_name; symbols; requires }
  in
  let axioms = List.rev registry.axioms in
  let lemmas = List.rev registry.checked_lemmas in
  let statements =
    List.map (statement `Axiom) axioms @ List.map (statement `Lemma) lemmas
  in
  let slice = Theory_slice.close ~roots statements in
  let selected_name name = List.mem name slice.statement_names in
  let selected_symbol symbol = List.mem symbol slice.symbols in
  let axioms =
    List.filter (fun axiom -> selected_name axiom.Typed_core.axiom_name) axioms
  in
  let checked_lemmas =
    List.filter (fun lemma -> selected_name lemma.Typed_core.axiom_name) lemmas
  in
  let proof_artifacts =
    List.rev registry.proof_artifacts
    |> List.filter (fun artifact -> selected_name artifact.lemma_name)
  in
  let logic_by_name = Hashtbl.create 16 in
  Hashtbl.iter
    (fun name (logic_symbol : Typed_core.logic_symbol) ->
      if selected_symbol logic_symbol.logic_name.key then
        Hashtbl.replace logic_by_name name logic_symbol)
    registry.logic_by_name;
  let datatypes =
    List.filter
      (fun (datatype : Typed_core.datatype) ->
        List.exists
          (fun (constructor : Typed_core.constructor) ->
            selected_symbol constructor.symbol.key)
          datatype.constructors)
      registry.datatypes
  in
  let registry =
    {
      registry with
      logic_by_name;
      axioms = List.rev axioms;
      checked_lemmas = List.rev checked_lemmas;
      proof_artifacts = List.rev proof_artifacts;
      datatypes;
    }
  in
  ({ program with registry }, slice.symbols)

type smt_value = { term : string; refinement : Generic_refinement.type_ option }

let typed_pattern_smt env scrutinee pattern =
  let rec translate env scrutinee = function
    | Typed_core.Pat_any -> ("true", env)
    | Pat_var symbol ->
        ("true", (symbol.key, { term = scrutinee; refinement = None }) :: env)
    | Pat_alias (inner, symbol) ->
        let guard, env = translate env scrutinee inner in
        (guard, (symbol.key, { term = scrutinee; refinement = None }) :: env)
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

type generic_call_state = {
  runtime_declarations : (string, string list * string) Hashtbl.t;
  mutable side_conditions : string list;
  mutable summary_assumptions : string list;
  mutable ghost_instantiations : string list;
  mutable used_theory_symbols : string list;
}

let new_generic_call_state () =
  {
    runtime_declarations = Hashtbl.create 8;
    side_conditions = [];
    summary_assumptions = [];
    ghost_instantiations = [];
    used_theory_symbols = [];
  }

let use_theory_symbol state symbol =
  if not (List.mem symbol state.used_theory_symbols) then
    state.used_theory_symbols <- symbol :: state.used_theory_symbols

let rec use_pattern_theory state = function
  | Typed_core.Pat_construct (constructor, patterns) ->
      use_theory_symbol state constructor.symbol.key;
      List.iter (use_pattern_theory state) patterns
  | Pat_tuple (_, patterns) -> List.iter (use_pattern_theory state) patterns
  | Pat_alias (pattern, _) -> use_pattern_theory state pattern
  | Pat_any | Pat_var _ | Pat_int _ | Pat_bool _ -> ()

let rec generic_term_smt =
  let open Generic_refinement in
  function
  | Integer integer -> string_of_int integer
  | Boolean boolean -> string_of_bool boolean
  | Variable variable -> smt_identifier variable
  | Not term -> app "not" [ generic_term_smt term ]
  | And terms -> and_ (List.map generic_term_smt terms)
  | Or terms -> or_ (List.map generic_term_smt terms)
  | Equal (left, right) ->
      app "=" [ generic_term_smt left; generic_term_smt right ]
  | Add (left, right) ->
      app "+" [ generic_term_smt left; generic_term_smt right ]
  | Greater (left, right) ->
      app ">" [ generic_term_smt left; generic_term_smt right ]
  | Apply (function_, argument) ->
      app (generic_term_smt function_) [ generic_term_smt argument ]
  | Generic generic -> invalid_arg ("unelaborated generic refinement " ^ generic)
  | Evar evar -> invalid_arg ("unsolved generic refinement " ^ evar)
  | Lambda _ -> invalid_arg "refinement lambda escaped beta-reduction"

let generic_error ~loc =
  let open Generic_refinement in
  function
  | Ill_sorted message | Type_mismatch message ->
      typed_error_at loc "%s" message
  | Ill_formed_hindley generic ->
      typed_error_at loc "Hindley generic `%s` is not value-dependent" generic
  | Ill_formed_horn generic ->
      typed_error_at loc "Horn generic `%s` is not in a positive position"
        generic
  | Arity_mismatch ->
      typed_error_at loc "generic scheme application arity mismatch"
  | Unsolved_hindley generic ->
      typed_error_at loc "Hindley generic `%s` was not solved by its arguments"
        generic
  | Unsolved_horn generic ->
      typed_error_at loc "Horn generic `%s` has no solvable lower bound" generic
  | Unsupported_horn_constraint generic ->
      typed_error_at loc "Horn constraints for `%s` left the positive fragment"
        generic
  | Horn_fixpoint_did_not_converge iterations ->
      typed_error_at loc "Horn fixpoint did not converge in %d iterations"
        iterations
  | Cyclic_instantiation evar ->
      typed_error_at loc "cyclic Hindley instantiation `%s`" evar

let generic_constraint_smt ~loc (constraint_ : Generic_refinement.constraint_) =
  try
    app "=>"
      [
        generic_term_smt constraint_.assumption;
        generic_term_smt constraint_.requirement;
      ]
  with Invalid_argument message ->
    typed_error_at loc "generic call constraint is not first-order: %s" message

let under_path path condition =
  match path with [] -> condition | _ -> app "=>" [ and_ path; condition ]

let instantiate_function_at_call ~loc (function_def : Typed_core.function_def)
    arguments result_sort =
  let open Typed_core in
  let substitutions = Sort_evars.create () in
  let unify formal actual =
    match Sort_evars.unify substitutions ~formal ~actual with
    | Ok () -> ()
    | Error (Occurs (variable, actual)) ->
        typed_error_at loc "cyclic call-site type instance `%s` in %s" variable
          (typed_smt_sort actual)
    | Error (Shape_mismatch (formal, actual)) ->
        typed_error_at loc "call-site type mismatch: expected %s but got %s"
          (typed_smt_sort formal) (typed_smt_sort actual)
  in
  List.iter2
    (fun (_, formal) (actual : Typed_core.expr) -> unify formal actual.sort)
    function_def.arguments arguments;
  unify function_def.result result_sort;
  let substitute = Sort_evars.substitute substitutions in
  let constructor (constructor : Typed_core.constructor) =
    {
      constructor with
      arguments = List.map substitute constructor.arguments;
      result = substitute constructor.result;
    }
  in
  let constructor_for_result constructor_ result =
    let constructor_ = constructor constructor_ in
    let local = Sort_evars.create () in
    match Sort_evars.unify local ~formal:constructor_.result ~actual:result with
    | Ok () ->
        let substitute = Sort_evars.substitute local in
        {
          constructor_ with
          arguments = List.map substitute constructor_.arguments;
          result;
        }
    | Error _ -> { constructor_ with result }
  in
  let rec pattern expected = function
    | Typed_core.Pat_tuple (_, patterns) ->
        let elements =
          match expected with
          | S_tuple elements when List.length elements = List.length patterns ->
              elements
          | _ -> List.map (fun _ -> S_unit) patterns
        in
        Pat_tuple (expected, List.map2 pattern elements patterns)
    | Pat_construct (constructor_, patterns) ->
        let constructor_ = constructor_for_result constructor_ expected in
        Pat_construct
          (constructor_, List.map2 pattern constructor_.arguments patterns)
    | Pat_alias (inner, symbol) -> Pat_alias (pattern expected inner, symbol)
    | (Pat_any | Pat_var _ | Pat_int _ | Pat_bool _) as pattern -> pattern
  in
  let rec map_expression (current : Typed_core.expr) =
    let sort = substitute current.sort in
    let desc =
      match current.desc with
      | (Var _ | Int _ | Bool _ | Raise _ | Deref _) as desc -> desc
      | Tuple expressions -> Tuple (List.map map_expression expressions)
      | Construct (constructor_, expressions) ->
          Construct
            ( constructor_for_result constructor_ sort,
              List.map map_expression expressions )
      | Choose expressions -> Choose (List.map map_expression expressions)
      | Apply (symbol, expressions) ->
          Apply (symbol, List.map map_expression expressions)
      | If (condition, if_true, if_false) ->
          If
            ( map_expression condition,
              map_expression if_true,
              map_expression if_false )
      | Let (symbol, value, body) ->
          Let (symbol, map_expression value, map_expression body)
      | Match (scrutinee, cases) ->
          let scrutinee = map_expression scrutinee in
          Match
            ( scrutinee,
              List.map
                (fun (pattern_, body) ->
                  (pattern scrutinee.sort pattern_, map_expression body))
                cases )
      | Record (constructor_, expressions) ->
          Record
            ( constructor_for_result constructor_ sort,
              List.map map_expression expressions )
      | Field (constructor_, index, record) ->
          let record = map_expression record in
          Field (constructor_for_result constructor_ record.sort, index, record)
      | Try (body, cases) ->
          Try
            ( map_expression body,
              List.map
                (fun (pattern, handler) -> (pattern, map_expression handler))
                cases )
      | Let_ref (symbol, sort, initial, body) ->
          Let_ref
            ( symbol,
              substitute sort,
              map_expression initial,
              map_expression body )
      | Assign (symbol, value) -> Assign (symbol, map_expression value)
      | Sequence (first, second) ->
          Sequence (map_expression first, map_expression second)
    in
    { current with desc; sort }
  in
  {
    function_def with
    arguments =
      List.map
        (fun (symbol, sort) -> (symbol, substitute sort))
        function_def.arguments;
    result = substitute function_def.result;
    body = map_expression function_def.body;
  }

let rec typed_expr_smt_with_choices (program : Typed_core.program) analysis mode
    current_function path call_stack choices generic_calls env expression =
  let registry = program.registry in
  let _sort = expression.Typed_core.sort in
  let recurse =
    typed_expr_smt_with_choices program analysis mode current_function path
      call_stack choices generic_calls env
  in
  let make ?(refinement = expression.Typed_core.refinement) term =
    { term; refinement }
  in
  let recurse_term expression = (recurse expression).term in
  match expression.Typed_core.desc with
  | Var symbol -> (
      match List.assoc_opt symbol.key env with
      | Some value -> (
          match expression.refinement with
          | Some refinement -> { value with refinement = Some refinement }
          | None -> value)
      | None ->
          typed_error_at expression.loc "unsupported global value `%s`"
            symbol.display)
  | Int value -> make (string_of_int value)
  | Bool value -> make (string_of_bool value)
  | Construct (constructor, arguments) | Record (constructor, arguments) ->
      use_theory_symbol generic_calls constructor.symbol.key;
      let arguments = List.map recurse_term arguments in
      make
        (if arguments = [] then typed_constructor_name constructor
         else app (typed_constructor_name constructor) arguments)
  | Choose [ left; right ] ->
      let name = "choice_" ^ string_of_int (List.length !choices) in
      choices := (name, Typed_core.S_bool) :: !choices;
      make (app "ite" [ name; recurse_term left; recurse_term right ])
  | Choose _ ->
      typed_error_at expression.loc
        "the MVP choose primitive currently requires exactly two alternatives"
  | Apply (symbol, arguments)
    when Hashtbl.mem program.registry.generic_schemes_by_name symbol.key ->
      let scheme =
        Hashtbl.find program.registry.generic_schemes_by_name symbol.key
      in
      let argument_values = List.map recurse arguments in
      let actual_types =
        List.map
          (fun ((argument : Typed_core.expr), value) ->
            match value.refinement with
            | Some refinement -> refinement
            | None ->
                typed_error_at argument.loc
                  "argument to generic `%s` needs [@refined.type]"
                  symbol.display)
          (List.combine arguments argument_values)
      in
      let elaboration =
        match Generic_refinement.elaborate_application scheme actual_types with
        | Ok elaboration -> elaboration
        | Error error -> generic_error ~loc:expression.loc error
      in
      let runtime_name = "F_" ^ smt_identifier symbol.key in
      Hashtbl.replace generic_calls.runtime_declarations runtime_name
        ( List.map
            (fun (argument : Typed_core.expr) -> typed_smt_sort argument.sort)
            arguments,
          typed_smt_sort expression.sort );
      generic_calls.side_conditions <-
        List.rev_append
          (List.map
             (fun constraint_ ->
               generic_constraint_smt ~loc:expression.loc constraint_
               |> under_path path)
             elaboration.constraints)
          generic_calls.side_conditions;
      generic_calls.ghost_instantiations <-
        List.rev_append
          (List.map
             (fun (instantiation : Generic_refinement.instantiation) ->
               Printf.sprintf "%s.%s=%s" symbol.display instantiation.generic
                 (Generic_refinement.string_of_term instantiation.refinement))
             elaboration.instantiations)
          generic_calls.ghost_instantiations;
      make ~refinement:(Some elaboration.result)
        (app runtime_name (List.map (fun value -> value.term) argument_values))
  | Apply (symbol, [ left; right ]) -> (
      match binary_operator symbol.display with
      | Some operator ->
          make (app operator [ recurse_term left; recurse_term right ])
      | None -> (
          match typed_lookup_logic registry [] symbol.key with
          | Some logic_symbol ->
              use_theory_symbol generic_calls logic_symbol.logic_name.key;
              if List.length logic_symbol.arguments <> 2 then
                typed_error_at expression.loc
                  "logical predicate `%s` has an unsupported application arity"
                  symbol.display;
              make
                (app
                   (typed_logic_name logic_symbol)
                   [ recurse_term left; recurse_term right ])
          | None ->
              typed_inline_call program analysis mode current_function path
                call_stack choices generic_calls env expression symbol
                [ left; right ]))
  | Apply (symbol, [ argument ]) when symbol.display = "not" ->
      make (app "not" [ recurse_term argument ])
  | Apply (symbol, _) -> (
      let arguments =
        match expression.desc with
        | Apply (_, arguments) -> arguments
        | _ -> assert false
      in
      match typed_lookup_logic registry [] symbol.key with
      | Some logic_symbol ->
          use_theory_symbol generic_calls logic_symbol.logic_name.key;
          if List.length arguments <> List.length logic_symbol.arguments then
            typed_error_at expression.loc
              "logical predicate `%s` has an unsupported application arity"
              symbol.display;
          make
            (app
               (typed_logic_name logic_symbol)
               (List.map recurse_term arguments))
      | None ->
          typed_inline_call program analysis mode current_function path
            call_stack choices generic_calls env expression symbol arguments)
  | If (condition, if_true, if_false) ->
      let condition = recurse condition in
      let branch branch_path branch =
        typed_expr_smt_with_choices program analysis mode current_function
          (branch_path :: path) call_stack choices generic_calls env branch
      in
      let if_true = branch condition.term if_true in
      let if_false = branch (app "not" [ condition.term ]) if_false in
      let refinement =
        if if_true.refinement = if_false.refinement then if_true.refinement
        else expression.refinement
      in
      make ~refinement
        (app "ite" [ condition.term; if_true.term; if_false.term ])
  | Let (symbol, value, body) ->
      let value = recurse value in
      typed_expr_smt_with_choices program analysis mode current_function path
        call_stack choices generic_calls
        ((symbol.key, value) :: env)
        body
  | Match (scrutinee, cases) ->
      let scrutinee = recurse_term scrutinee in
      List.iter
        (fun (pattern, _) -> use_pattern_theory generic_calls pattern)
        cases;
      let translated =
        let rec translate previous = function
          | [] -> []
          | (pattern, body) :: rest ->
              let guard, case_env = typed_pattern_smt env scrutinee pattern in
              let effective_guard =
                match previous with
                | [] -> guard
                | _ -> and_ [ guard; app "not" [ or_ previous ] ]
              in
              let body =
                typed_expr_smt_with_choices program analysis mode
                  current_function (effective_guard :: path) call_stack choices
                  generic_calls case_env body
              in
              (guard, body) :: translate (guard :: previous) rest
        in
        translate [] cases
      in
      let refinement =
        match translated with
        | [] -> expression.refinement
        | (_, first) :: rest ->
            if
              List.for_all
                (fun (_, value) -> value.refinement = first.refinement)
                rest
            then first.refinement
            else expression.refinement
      in
      let rec tree = function
        | [] -> typed_error_at expression.loc "empty match"
        | [ (_, body) ] -> body.term
        | (guard, body) :: rest -> app "ite" [ guard; body.term; tree rest ]
      in
      make ~refinement (tree translated)
  | Field (constructor, index, record) ->
      use_theory_symbol generic_calls constructor.symbol.key;
      make (app (typed_selector constructor index) [ recurse_term record ])
  | Tuple elements ->
      make
        (app
           (typed_tuple_constructor expression.sort)
           (List.map recurse_term elements))
  | Raise _ | Try _ | Let_ref _ | Deref _ | Assign _ | Sequence _ ->
      typed_error_at expression.loc
        "exception outcome escaped the relational translator"

and typed_inline_call program analysis mode current_function path call_stack
    choices generic_calls env expression symbol arguments =
  let function_def =
    List.find_opt
      (fun (function_def : Typed_core.function_def) ->
        function_def.symbol.key = symbol.Typed_core.key)
      program.Typed_core.functions
  in
  match function_def with
  | None ->
      typed_error_at expression.Typed_core.loc
        "call to `%s` needs a refinement summary" symbol.display
  | Some function_def ->
      if List.length arguments <> List.length function_def.arguments then
        typed_error_at expression.loc
          "call to `%s` has unsupported partial arity" symbol.display;
      let function_def =
        instantiate_function_at_call ~loc:expression.loc function_def arguments
          expression.sort
      in
      let call_program = typed_monomorphize_datatypes program function_def in
      List.iter
        (fun (datatype : Typed_core.datatype) ->
          if
            not
              (List.exists
                 (fun (existing : Typed_core.datatype) ->
                   existing.owner = datatype.owner)
                 program.registry.datatypes)
          then
            program.registry.datatypes <- datatype :: program.registry.datatypes)
        call_program.registry.datatypes;
      let values =
        List.map
          (typed_expr_smt_with_choices program analysis mode current_function
             path call_stack choices generic_calls env)
          arguments
      in
      let terms = List.map (fun value -> value.term) values in
      let recursive =
        Function_analysis.is_recursive_edge analysis
          ~caller:current_function.Typed_core.symbol.key ~callee:symbol.key
      in
      let over_contracts =
        List.filter
          (fun (contract : Typed_core.contract) -> contract.mode = Over)
          function_def.contracts
      in
      let constructive_under_contracts =
        List.filter
          (fun (contract : Typed_core.contract) ->
            contract.mode = Under && contract.witnesses <> [])
          function_def.contracts
      in
      if mode = Over && over_contracts <> [] then (
        let summary =
          match over_contracts with
          | [ summary ] -> summary
          | _ ->
              typed_error_at expression.loc
                "call to `%s` has ambiguous safety summaries" symbol.display
        in
        let result = "call_result_" ^ string_of_int (List.length !choices) in
        choices := (result, function_def.result) :: !choices;
        let formula_env =
          List.map2
            (fun ((argument : Typed_core.symbol), sort) term ->
              (argument.display, (term, sort)))
            function_def.arguments terms
        in
        let translate formula =
          let formula =
            parse_formula ~filename:summary.loc.file
              ~loc:(location_of_span summary.loc)
              formula
          in
          formula_theory_symbols program.registry formula_env formula
          |> List.iter (use_theory_symbol generic_calls);
          typed_formula program.registry formula_env formula
        in
        let pre = translate summary.pre in
        let post =
          let formula =
            parse_formula ~filename:summary.loc.file
              ~loc:(location_of_span summary.loc)
              summary.post
          in
          formula_theory_symbols program.registry
            (("result", (result, function_def.result)) :: formula_env)
            formula
          |> List.iter (use_theory_symbol generic_calls);
          typed_formula program.registry
            (("result", (result, function_def.result)) :: formula_env)
            formula
        in
        generic_calls.side_conditions <-
          under_path path pre :: generic_calls.side_conditions;
        generic_calls.summary_assumptions <-
          under_path path post :: generic_calls.summary_assumptions;
        (if recursive then
           let callee_measure =
             match function_def.measure with
             | Some measure -> measure
             | None ->
                 typed_error_at expression.loc
                   "recursive callee `%s` needs [@refined.measure]"
                   symbol.display
           in
           let caller_measure =
             match current_function.Typed_core.measure with
             | Some measure -> measure
             | None ->
                 typed_error_at expression.loc
                   "recursive caller `%s` needs [@refined.measure]"
                   current_function.symbol.display
           in
           let callee_measure_term =
             List.find_map
               (fun (((argument : Typed_core.symbol), _), term) ->
                 if argument.key = callee_measure.key then Some term else None)
               (List.combine function_def.arguments terms)
             |> Option.get
           in
           let caller_measure_term =
             match List.assoc_opt caller_measure.key env with
             | Some value -> value.term
             | None -> assert false
           in
           generic_calls.side_conditions <-
             under_path path
               (and_
                  [
                    app ">=" [ caller_measure_term; "0" ];
                    app "<" [ callee_measure_term; caller_measure_term ];
                  ])
             :: generic_calls.side_conditions);
        { term = result; refinement = expression.refinement })
      else if mode = Under && constructive_under_contracts <> [] then (
        let summary =
          match constructive_under_contracts with
          | [ summary ] -> summary
          | _ ->
              typed_error_at expression.loc
                "call to `%s` has ambiguous constructive coverage summaries"
                symbol.display
        in
        let formal_names =
          List.map
            (fun ((argument : Typed_core.symbol), _) -> argument.display)
            function_def.arguments
        in
        if
          List.sort String.compare (List.map fst summary.witnesses)
          <> List.sort String.compare formal_names
        then
          typed_error_at expression.loc
            "coverage summary for `%s` has incomplete witnesses" symbol.display;
        let result = "call_result_" ^ string_of_int (List.length !choices) in
        choices := (result, function_def.result) :: !choices;
        let result_env = [ ("result", (result, function_def.result)) ] in
        let parse text =
          parse_formula ~filename:summary.loc.file
            ~loc:(location_of_span summary.loc)
            text
        in
        let post_formula = parse summary.post in
        formula_theory_symbols program.registry result_env post_formula
        |> List.iter (use_theory_symbol generic_calls);
        let constraints =
          typed_formula program.registry result_env post_formula
          :: List.map2
               (fun ((formal : Typed_core.symbol), sort) actual ->
                 let witness =
                   parse (List.assoc formal.display summary.witnesses)
                 in
                 formula_theory_symbols ~expected:sort program.registry
                   result_env witness
                 |> List.iter (use_theory_symbol generic_calls);
                 app "="
                   [
                     actual;
                     typed_formula ~expected:sort program.registry result_env
                       witness;
                   ])
               function_def.arguments terms
        in
        generic_calls.summary_assumptions <-
          List.rev_append
            (List.map (under_path path) constraints)
            generic_calls.summary_assumptions;
        (if recursive then
           let callee_measure =
             match function_def.measure with
             | Some measure -> measure
             | None ->
                 typed_error_at expression.loc
                   "recursive coverage callee `%s` needs [@refined.measure]"
                   symbol.display
           in
           let caller_measure =
             match current_function.Typed_core.measure with
             | Some measure -> measure
             | None ->
                 typed_error_at expression.loc
                   "recursive coverage caller `%s` needs [@refined.measure]"
                   current_function.symbol.display
           in
           let callee =
             List.find_map
               (fun (((argument : Typed_core.symbol), _), term) ->
                 if argument.key = callee_measure.key then Some term else None)
               (List.combine function_def.arguments terms)
             |> Option.get
           in
           let caller = (List.assoc caller_measure.key env).term in
           generic_calls.summary_assumptions <-
             under_path path
               (and_ [ app ">=" [ caller; "0" ]; app "<" [ callee; caller ] ])
             :: generic_calls.summary_assumptions);
        { term = result; refinement = expression.refinement })
      else if recursive then
        typed_error_at expression.loc
          (if mode = Under then
             "recursive coverage call to `%s` needs a compositional \
              under-summary"
           else "recursive call to `%s` needs one safety summary")
          symbol.display
      else
        let call_env =
          List.map2
            (fun (argument, _) term -> (argument.Typed_core.key, term))
            function_def.arguments values
        in
        typed_expr_smt_with_choices program analysis mode function_def path
          (symbol.key :: call_stack) choices generic_calls call_env
          function_def.body

let typed_expr_smt program analysis mode function_def env expression =
  let choices = ref [] in
  let generic_calls = new_generic_call_state () in
  let term =
    typed_expr_smt_with_choices program analysis mode function_def [] [] choices
      generic_calls env expression
  in
  (term, List.rev !choices, generic_calls)

let rec typed_has_exception (expression : Typed_core.expr) =
  match expression.desc with
  | Raise _ | Try _ | Let_ref _ | Deref _ | Assign _ | Sequence _ -> true
  | Var _ | Int _ | Bool _ -> false
  | Tuple expressions
  | Construct (_, expressions)
  | Choose expressions
  | Apply (_, expressions)
  | Record (_, expressions) ->
      List.exists typed_has_exception expressions
  | If (condition, if_true, if_false) ->
      List.exists typed_has_exception [ condition; if_true; if_false ]
  | Let (_, value, body) ->
      typed_has_exception value || typed_has_exception body
  | Match (scrutinee, cases) ->
      typed_has_exception scrutinee
      || List.exists (fun (_, body) -> typed_has_exception body) cases
  | Field (_, _, record) -> typed_has_exception record

let typed_local_cells expression =
  let rec collect cells (expression : Typed_core.expr) =
    match expression.desc with
    | Let_ref (symbol, sort, initial, body) ->
        collect
          ((symbol.display, symbol.key, sort) :: collect cells initial)
          body
    | Let (_, value, body) | Sequence (value, body) ->
        collect (collect cells value) body
    | If (condition, if_true, if_false) ->
        collect (collect (collect cells condition) if_true) if_false
    | Try (body, cases) ->
        List.fold_left
          (fun cells (_, handler) -> collect cells handler)
          (collect cells body) cases
    | Match (body, cases) ->
        List.fold_left
          (fun cells (_, handler) -> collect cells handler)
          (collect cells body) cases
    | Tuple expressions
    | Construct (_, expressions)
    | Choose expressions
    | Apply (_, expressions)
    | Record (_, expressions) ->
        List.fold_left collect cells expressions
    | Assign (_, value) | Field (_, _, value) -> collect cells value
    | Var _ | Int _ | Bool _ | Raise _ | Deref _ -> cells
  in
  collect [] expression |> List.sort_uniq compare

let typed_relational_expr program analysis function_def env expression =
  let module R = Relational_outcome in
  let choices = ref [] in
  let generic_calls = new_generic_call_state () in
  let rec translate env state (expression : Typed_core.expr) =
    match expression.desc with
    | Raise exception_ -> R.raise_ ~state exception_.display
    | If (condition, if_true, if_false) ->
        if typed_has_exception condition then
          typed_error_at condition.loc
            "exceptionful conditions are not yet supported";
        let condition =
          typed_expr_smt_with_choices program analysis Over function_def [] []
            choices generic_calls env condition
        in
        R.branch ~condition:condition.term
          ~if_true:(translate env state if_true)
          ~if_false:(translate env state if_false)
    | Let (symbol, value, body) ->
        R.bind (translate env state value) (fun value state ->
            translate
              ((symbol.key, { term = value; refinement = None }) :: env)
              state body)
    | Try (body, cases) ->
        R.try_with (translate env state body) (fun exception_ state ->
            match
              List.find_opt
                (fun (pattern, _) ->
                  match pattern with
                  | Typed_core.Exn_any -> true
                  | Exn symbol -> symbol.display = exception_)
                cases
            with
            | Some (_, handler) -> translate env state handler
            | None -> R.raise_ ~state exception_)
    | Let_ref (symbol, _sort, initial, body) ->
        R.bind (translate env state initial) (fun value state ->
            translate env ((symbol.key, value) :: state) body)
    | Deref symbol ->
        if not (List.mem_assoc symbol.key state) then
          typed_error_at expression.loc
            "reference `%s` is not a local non-escaping cell" symbol.display;
        R.read ~state ~cell:symbol.key
    | Assign (symbol, value) ->
        if not (List.mem_assoc symbol.key state) then
          typed_error_at expression.loc
            "reference `%s` is not a local non-escaping cell" symbol.display;
        R.bind (translate env state value) (fun value state ->
            R.write ~state ~cell:symbol.key ~value)
    | Sequence (first, second) ->
        R.bind (translate env state first) (fun _ state ->
            translate env state second)
    | _ ->
        if typed_has_exception expression then
          typed_error_at expression.loc
            "exception is nested in an unsupported evaluation context";
        let value =
          typed_expr_smt_with_choices program analysis Over function_def [] []
            choices generic_calls env expression
        in
        R.return ~state value.term
  in
  (translate env [] expression, List.rev !choices, generic_calls)

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
  let set =
    List.fold_left
      (fun set (lemma : Typed_core.axiom) ->
        List.fold_left (fun set (_, sort) -> add set sort) set lemma.variables)
      set program.registry.checked_lemmas
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
  List.iter
    (fun (lemma : Typed_core.axiom) ->
      List.iter (fun (_, sort) -> add sort) lemma.variables)
    program.registry.checked_lemmas;
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
  List.iter
    (fun (datatype : Typed_core.datatype) ->
      line "(declare-sort %s 0)" (typed_smt_sort datatype.Typed_core.owner))
    program.registry.datatypes;
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
  let emit_statement provenance (axiom : Typed_core.axiom) =
    let formula =
      parse_formula ~filename:axiom.loc.file
        ~loc:(location_of_span axiom.loc)
        axiom.body
    in
    let env =
      List.map
        (fun (name, sort) -> (name, (smt_identifier name, sort)))
        axiom.variables
    in
    let body = typed_formula ~scope:axiom.scope program.registry env formula in
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
    line "; %s: %s" provenance axiom.axiom_name;
    line "(assert %s)" assertion
  in
  List.rev program.registry.axioms |> List.iter (emit_statement "trusted axiom");
  List.rev program.registry.checked_lemmas
  |> List.iter (emit_statement "checked lemma");
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

let typed_obligation (program : Typed_core.program) analysis
    (function_def : Typed_core.function_def) (contract : Typed_core.contract) =
  let env =
    List.map
      (fun (symbol, _) ->
        ( symbol.Typed_core.key,
          { term = smt_identifier symbol.key; refinement = None } ))
      function_def.Typed_core.arguments
  in
  let formula_env =
    List.map2
      (fun (symbol, sort) (_, value) ->
        (symbol.Typed_core.display, (value.term, sort)))
      function_def.arguments env
  in
  let pre_expression =
    parse_formula ~filename:contract.loc.file
      ~loc:(location_of_span contract.loc)
      contract.pre
  in
  let post_expression =
    parse_formula ~filename:contract.loc.file
      ~loc:(location_of_span contract.loc)
      contract.post
  in
  let witness_expressions =
    match contract.witnesses with
    | [] -> []
    | witnesses ->
        if contract.mode <> Under then assert false;
        let names = List.map fst witnesses in
        let expected =
          List.map
            (fun ((symbol : Typed_core.symbol), _) -> symbol.display)
            function_def.arguments
        in
        if
          List.sort String.compare names <> List.sort String.compare expected
          || List.length names
             <> List.length (List.sort_uniq String.compare names)
        then
          typed_error_at contract.loc
            "coverage witnesses must define every parameter exactly once";
        List.map
          (fun ((symbol : Typed_core.symbol), sort) ->
            let text = List.assoc symbol.display witnesses in
            let expression =
              parse_formula ~filename:contract.loc.file
                ~loc:(location_of_span contract.loc)
                text
            in
            (symbol, sort, expression))
          function_def.arguments
  in
  let program =
    typed_specialize_program program function_def pre_expression post_expression
  in
  let program = typed_monomorphize_datatypes program function_def in
  let body, choices, generic_calls =
    typed_expr_smt program analysis contract.mode function_def env
      function_def.body
  in
  let roots =
    generic_calls.used_theory_symbols
    @ formula_theory_symbols program.registry formula_env pre_expression
    @ formula_theory_symbols program.registry
        (("result", ("result", function_def.result)) :: formula_env)
        post_expression
    @ List.concat_map
        (fun (_, sort, expression) ->
          formula_theory_symbols ~expected:sort program.registry
            [ ("result", ("missing_result", function_def.result)) ]
            expression)
        witness_expressions
    |> List.sort_uniq String.compare
  in
  let program, _enabled_symbols = slice_program_theory program ~roots in
  let pre = typed_formula program.registry formula_env pre_expression in
  let result_name =
    match contract.mode with Over -> "result" | Under -> "missing_result"
  in
  let post_env =
    let result = ("result", (result_name, function_def.result)) in
    if witness_expressions = [] then result :: formula_env else [ result ]
  in
  let post = typed_formula program.registry post_env post_expression in
  let argument_witnesses =
    List.map
      (fun (symbol, sort, expression) ->
        ( smt_identifier symbol.Typed_core.key,
          typed_formula ~expected:sort program.registry
            [ ("result", (result_name, function_def.result)) ]
            expression ))
      witness_expressions
  in
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer
    "(set-option :produce-models true)\n(set-logic ALL)\n";
  Buffer.add_string buffer (typed_datatype_prelude program function_def);
  Hashtbl.iter
    (fun name (arguments, result) ->
      Buffer.add_string buffer
        (Printf.sprintf "(declare-fun %s (%s) %s)\n" name
           (String.concat " " arguments)
           result))
    generic_calls.runtime_declarations;
  Vc_semantics.encode contract.mode
    {
      buffer;
      arguments =
        List.map
          (fun (symbol, sort) ->
            (smt_identifier symbol.Typed_core.key, typed_smt_sort sort))
          function_def.arguments;
      choices =
        List.map (fun (name, sort) -> (name, typed_smt_sort sort)) choices;
      result_sort = typed_smt_sort function_def.result;
      body = body.term;
      pre;
      post;
      assumptions = List.rev generic_calls.summary_assumptions;
      side_conditions = List.rev generic_calls.side_conditions;
      argument_witnesses;
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
    checked_lemmas =
      List.rev_map
        (fun (lemma : Typed_core.axiom) -> lemma.axiom_name)
        program.registry.checked_lemmas;
    proof_artifacts = List.rev program.registry.proof_artifacts;
    ghost_instantiations = List.rev generic_calls.ghost_instantiations;
  }

let typed_exception_obligation (program : Typed_core.program) analysis
    (function_def : Typed_core.function_def) (contract : Typed_core.contract) =
  if contract.mode <> Over then
    typed_error_at contract.loc
      "exceptionful coverage contracts are not yet supported";
  let env =
    List.map
      (fun (symbol, _) ->
        ( symbol.Typed_core.key,
          { term = smt_identifier symbol.key; refinement = None } ))
      function_def.arguments
  in
  let formula_env =
    List.map2
      (fun (symbol, sort) (_, value) ->
        (symbol.Typed_core.display, (value.term, sort)))
      function_def.arguments env
  in
  let parse text =
    parse_formula ~filename:contract.loc.file
      ~loc:(location_of_span contract.loc)
      text
  in
  let pre_expression = parse contract.pre in
  let post_expression = parse contract.post in
  let raised_expressions =
    contract.raises
    |> List.map (fun (name, predicate) -> (name, parse predicate))
  in
  let local_cells = typed_local_cells function_def.body in
  let state_expressions =
    List.map
      (fun (name, predicate) ->
        match List.find_opt (fun (cell, _, _) -> cell = name) local_cells with
        | Some (_, key, sort) -> (name, key, sort, parse predicate)
        | None ->
            typed_error_at contract.loc
              "state postcondition names unknown local cell `%s`" name)
      contract.state
  in
  let state_names = List.map fst contract.state in
  if
    List.length state_names
    <> List.length (List.sort_uniq String.compare state_names)
  then typed_error_at contract.loc "state clauses must name each cell once";
  let names = List.map fst contract.raises in
  if List.length names <> List.length (List.sort_uniq String.compare names) then
    typed_error_at contract.loc "raises clauses must name each exception once";
  let program =
    typed_specialize_program program function_def pre_expression post_expression
    |> fun program -> typed_monomorphize_datatypes program function_def
  in
  let relation, choices, generic_calls =
    typed_relational_expr program analysis function_def env function_def.body
  in
  if
    generic_calls.side_conditions <> []
    || generic_calls.summary_assumptions <> []
  then
    typed_error_at contract.loc
      "exceptionful calls with refinement summaries are not yet supported";
  let roots =
    generic_calls.used_theory_symbols
    @ formula_theory_symbols program.registry formula_env pre_expression
    @ formula_theory_symbols program.registry
        (("result", ("result", function_def.result)) :: formula_env)
        post_expression
    @ List.concat_map
        (fun (_, expression) ->
          formula_theory_symbols program.registry formula_env expression)
        raised_expressions
    @ List.concat_map
        (fun (_, _, sort, expression) ->
          formula_theory_symbols program.registry
            (("value", ("state_value", sort))
            :: ("result", ("result", function_def.result))
            :: formula_env)
            expression)
        state_expressions
    |> List.sort_uniq String.compare
  in
  let program, _ = slice_program_theory program ~roots in
  let pre = typed_formula program.registry formula_env pre_expression in
  let post =
    typed_formula program.registry
      (("result", ("result", function_def.result)) :: formula_env)
      post_expression
  in
  let raised =
    List.map
      (fun (name, expression) ->
        (name, typed_formula program.registry formula_env expression))
      raised_expressions
  in
  let state_posts =
    List.map
      (fun (name, key, sort, expression) ->
        ( name,
          key,
          typed_formula program.registry
            (("value", ("state_value", sort))
            :: ("result", ("result", function_def.result))
            :: formula_env)
            expression ))
      state_expressions
  in
  let obligation =
    Relational_outcome.safety_obligation ~pre
      ~normal:(fun ~value ~initial:_ ~final ->
        let state_obligations =
          List.map
            (fun (_name, key, predicate) ->
              match List.assoc_opt key final with
              | Some state_value ->
                  Printf.sprintf "(let ((result %s) (state_value %s)) %s)" value
                    state_value predicate
              | None -> "false")
            state_posts
        in
        Printf.sprintf "(let ((result %s)) %s)" value
          (and_ (post :: state_obligations)))
      ~raised:(fun ~exception_ ~initial:_ ~final:_ ->
        Option.value (List.assoc_opt exception_ raised) ~default:"false")
      ~performed:(fun ~operation:_ ~payload:_ ~initial:_ ~final:_ -> "false")
      relation
  in
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer
    "(set-option :produce-models true)\n(set-logic ALL)\n";
  Buffer.add_string buffer (typed_datatype_prelude program function_def);
  List.iter
    (fun (symbol, sort) ->
      Buffer.add_string buffer
        (Printf.sprintf "(declare-const %s %s)\n"
           (smt_identifier symbol.Typed_core.key)
           (typed_smt_sort sort)))
    function_def.arguments;
  List.iter
    (fun (name, sort) ->
      Buffer.add_string buffer
        (Printf.sprintf "(declare-const %s %s)\n" name (typed_smt_sort sort)))
    choices;
  Buffer.add_string buffer (Printf.sprintf "(assert (not %s))\n" obligation);
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
    checked_lemmas =
      List.rev_map
        (fun (lemma : Typed_core.axiom) -> lemma.axiom_name)
        program.registry.checked_lemmas;
    proof_artifacts = List.rev program.registry.proof_artifacts;
    ghost_instantiations = List.rev generic_calls.ghost_instantiations;
  }

let lemma_obligations registry lemmas =
  let registry =
    {
      registry with
      Typed_core.lemmas = [];
      checked_lemmas = [];
      proof_artifacts = [];
    }
  in
  let obligation (lemma : Typed_core.axiom) =
    let arguments =
      List.map
        (fun (name, sort) ->
          ( Typed_core.
              { key = "lemma." ^ lemma.axiom_name ^ "." ^ name; display = name },
            sort ))
        lemma.variables
    in
    let dummy =
      Typed_core.
        {
          symbol =
            { key = "lemma." ^ lemma.axiom_name; display = lemma.axiom_name };
          arguments;
          result = S_unit;
          body =
            {
              desc = Bool true;
              sort = S_bool;
              refinement = None;
              loc = lemma.loc;
            };
          contracts = [];
          measure = None;
        }
    in
    let formula =
      parse_formula ~filename:lemma.loc.file
        ~loc:(location_of_span lemma.loc)
        lemma.body
    in
    let env =
      List.map
        (fun (name, sort) -> (name, (smt_identifier name, sort)))
        lemma.variables
    in
    let roots =
      formula_theory_symbols ~scope:lemma.scope registry env formula
    in
    let program = Typed_core.{ registry; functions = [] } in
    let program, _enabled_symbols = slice_program_theory program ~roots in
    let sliced_registry = program.Typed_core.registry in
    let body = typed_formula ~scope:lemma.scope sliced_registry env formula in
    let binders =
      String.concat " "
        (List.map
           (fun (name, sort) ->
             Printf.sprintf "(%s %s)" (smt_identifier name)
               (typed_smt_sort sort))
           lemma.variables)
    in
    let theorem =
      if lemma.variables = [] then body
      else app "forall" [ "(" ^ binders ^ ")"; body ]
    in
    let buffer = Buffer.create 4096 in
    Buffer.add_string buffer
      "(set-option :produce-models true)\n(set-logic ALL)\n";
    Buffer.add_string buffer (typed_datatype_prelude program dummy);
    Buffer.add_string buffer (Printf.sprintf "(assert (not %s))\n" theorem);
    Buffer.add_string buffer "(check-sat)\n(get-model)\n";
    {
      name = lemma.axiom_name;
      mode = Over;
      location = lemma.loc;
      smt = Buffer.contents buffer;
      trusted_axioms =
        List.rev_map
          (fun (axiom : Typed_core.axiom) -> axiom.axiom_name)
          sliced_registry.axioms;
      checked_lemmas =
        List.rev_map
          (fun (lemma : Typed_core.axiom) -> lemma.axiom_name)
          sliced_registry.checked_lemmas;
      proof_artifacts = List.rev sliced_registry.proof_artifacts;
      ghost_instantiations = [];
    }
  in
  List.map
    (fun lemma ->
      let result = obligation lemma in
      registry.checked_lemmas <- lemma :: registry.checked_lemmas;
      result)
    lemmas

let obligations_of_cmt_with_theories ~theories filename =
  let program = Ocaml_5_3_frontend.program_of_cmt ~theories filename in
  let analysis = Function_analysis.analyze program in
  List.concat_map
    (fun function_def ->
      List.map
        (fun contract ->
          if typed_has_exception function_def.Typed_core.body then
            typed_exception_obligation program analysis function_def contract
          else typed_obligation program analysis function_def contract)
        function_def.Typed_core.contracts)
    program.functions

let obligations_of_cmt filename =
  obligations_of_cmt_with_theories ~theories:[] filename
