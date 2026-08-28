module Strings = Set.Make (String)

type statement = {
  name : string;
  symbols : string list;
  requires : string list;
}

type result = { statement_names : string list; symbols : string list }

let close ~roots statements =
  let rec iterate symbols names =
    let symbols', names', changed =
      List.fold_left
        (fun (symbols, names, changed) statement ->
          let selected =
            Strings.mem statement.name names
            || List.exists
                 (fun symbol -> Strings.mem symbol symbols)
                 statement.symbols
          in
          if not selected then (symbols, names, changed)
          else
            let symbols' =
              List.fold_left
                (fun symbols symbol -> Strings.add symbol symbols)
                symbols statement.symbols
            in
            let names' =
              List.fold_left
                (fun names name -> Strings.add name names)
                (Strings.add statement.name names)
                statement.requires
            in
            ( symbols',
              names',
              changed
              || (not (Strings.equal symbols symbols'))
              || not (Strings.equal names names') ))
        (symbols, names, false) statements
    in
    if changed then iterate symbols' names' else (symbols', names')
  in
  let symbols, names =
    iterate
      (List.fold_left
         (fun symbols symbol -> Strings.add symbol symbols)
         Strings.empty roots)
      Strings.empty
  in
  {
    statement_names =
      List.filter_map
        (fun statement ->
          if Strings.mem statement.name names then Some statement.name else None)
        statements;
    symbols = Strings.elements symbols;
  }
