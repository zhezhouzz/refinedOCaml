type t = int

let equal left right = left = right

module Core = struct
  let holds _value = true
end

module Alias = Core
