type position = { offset : int; line : int; column : int }
type t = { file : string; start : position; finish : position }

let none =
  {
    file = "";
    start = { offset = 0; line = 1; column = 0 };
    finish = { offset = 0; line = 1; column = 0 };
  }
