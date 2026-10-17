exception Parser_error of string

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

let pp_sep fmt () = Format.pp_print_string fmt ", "
let pp_array pp_elem fmt arr =
  let open Format in
  pp_open_box fmt 0;
  pp_print_string fmt "[";
  pp_print_list ~pp_sep pp_elem fmt (Array.to_list arr);
  pp_print_string fmt "]";
  pp_close_box fmt ()

let combine_drop l1 l2 =
  let l1_len = List.length l1 in
  let l2_len = List.length l2 in
  if l1_len > l2_len then List.combine (CCList.drop (l1_len - l2_len) l1) l2
  else if l2_len > l1_len then
    List.combine l1 (CCList.drop (l2_len - l1_len) l2)
  else List.combine l1 l2
