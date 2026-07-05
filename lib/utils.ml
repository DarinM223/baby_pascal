module IntSet = struct
  include CCSet.Make (Int)
  let pp = pp CCInt.pp
end
module IntMap = struct
  include CCMap.Make (Int)
  let pp pp_v = pp CCInt.pp pp_v
end
module IntHashtbl = Hashtbl.Make (CCInt)

let split_list (i : int) l =
  let rec go acc = function
    | 0, x :: xs -> (List.rev (x :: acc), xs)
    | i, x :: xs -> go (x :: acc) (i - 1, xs)
    | _, [] -> raise Not_found
  in
  go [] (i, l)
