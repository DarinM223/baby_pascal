module IntSet = struct
  include CCSet.Make (Int)
  let pp = pp CCInt.pp
end
module IntMap = struct
  include CCMap.Make (Int)
  let pp pp_v = pp CCInt.pp pp_v
end
module IntHashtbl = CCHashtbl.Make (CCInt)

let hashtbl_size = 100

let pp_array pp_elem fmt arr =
  let open Format in
  pp_open_box fmt 0;
  pp_print_string fmt "[";
  pp_print_list
    ~pp_sep:(fun fmt () -> pp_print_string fmt ", ")
    pp_elem fmt (Array.to_list arr);
  pp_print_string fmt "]";
  pp_close_box fmt ()
