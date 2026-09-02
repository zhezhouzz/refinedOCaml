type statement = {
  name : string;
  symbols : string list;
  triggers : string list;
  propagates : string list;
  requires : string list;
}

type result = { statement_names : string list; symbols : string list }

val close : roots:string list -> statement list -> result
