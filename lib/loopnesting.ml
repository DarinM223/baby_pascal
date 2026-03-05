module LabelSet = struct
  include CCSet.Make (Int)
  let pp = pp Format.pp_print_int
end
module LabelMap = struct
  include CCMap.Make (Int)
  let pp pp_v = pp Format.pp_print_int pp_v
end
module type S = sig
  module Dom : Dominator.S
  module PositionSet : sig
    include CCSet.S with type elt = Dom.position
    val pp : t CCSet.printer
  end
  val loop_headers : PositionSet.t
end
module Make
    (G : Graph.S)
    (Dom :
      Dominator.S
        with type label = G.label
         and type graph = G.graph
         and type position = int) : S with module Dom = Dom = struct
  module Dom = Dom
  module PositionSet = struct
    include CCSet.Make (struct
      type t = Dom.position
      let compare = compare
    end)
    let pp = pp Dom.pp_position
  end

  let back_preds = Array.make Dom.size PositionSet.empty
  let non_back_preds = Array.make Dom.size PositionSet.empty
  let link = Array.init Dom.size (fun p -> p)
  let _find n =
    let n = ref n in
    while link.(!n) <> !n do
      n := link.(!n)
    done;
    !n
  let _union n m =
    let n = ref n in
    while link.(!n) <> !n do
      n := link.(!n)
    done;
    link.(!n) <- m

  let loop_headers =
    let result = ref PositionSet.empty in
    for i = 0 to Dom.size - 1 do
      let headers, nonheaders =
        List.partition (fun succ -> Dom.dominates succ i) (Dom.successors i)
      in
      List.iter
        (fun p -> back_preds.(p) <- PositionSet.add i back_preds.(p))
        headers;
      List.iter
        (fun p -> non_back_preds.(p) <- PositionSet.add i non_back_preds.(p))
        nonheaders;
      result :=
        List.fold_left (fun acc p -> PositionSet.add p acc) !result headers
    done;
    !result
end
