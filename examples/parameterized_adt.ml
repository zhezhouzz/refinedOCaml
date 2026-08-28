type 'a box = Box of 'a
type 'a cell = { value : 'a }
type 'a tree = Leaf of 'a | Node of 'a tree * 'a tree

let wrap value = Box value
let unwrap box = match box with Box value -> value
let make_cell value = { value }
let get_cell cell = cell.value

let[@refined.over { pre = "true"; post = "result = Box x" }] int_box (x : int) :
    int box =
  wrap x

let[@refined.over { pre = "true"; post = "result = Box x" }] bool_box (x : bool)
    : bool box =
  wrap x

let[@refined.over { pre = "true"; post = "result = x" }] int_roundtrip (x : int)
    : int =
  unwrap (wrap x)

let[@refined.over { pre = "true"; post = "result.value = x" }] int_cell
    (x : int) : int cell =
  make_cell x

let[@refined.over { pre = "true"; post = "result = x" }] bool_cell_roundtrip
    (x : bool) : bool =
  get_cell (make_cell x)

let[@refined.over { pre = "true"; post = "true" }] int_tree (x : int) : int tree
    =
  Node (Leaf x, Leaf x)

let[@refined.over { pre = "true"; post = "true" }] both_boxes (x : int)
    (flag : bool) : int box * bool box =
  (Box x, Box flag)

let[@refined.over { pre = "true"; post = "result = input" }] opaque_box
    (input : int box) : int box =
  input
