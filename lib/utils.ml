module IntSet = struct
  include CCSet.Make (Int)
  let pp = pp CCInt.pp
end
module IntMap = struct
  include CCMap.Make (Int)
  let pp pp_v = pp CCInt.pp pp_v
end
module IntHashtbl = Hashtbl.Make (CCInt)
