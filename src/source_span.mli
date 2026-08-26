type position = { offset : int; line : int; column : int }
type t = { file : string; start : position; finish : position }

val none : t
