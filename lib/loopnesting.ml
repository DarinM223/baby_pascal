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
  val loop_nodes : PositionSet.t iarray
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
  let header = Array.make Dom.size 0
  let find n =
    let n = ref n in
    while link.(!n) <> !n do
      n := link.(!n)
    done;
    !n
  let union n m =
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

  let _ =
    for w = Dom.size - 1 downto 0 do
      let p = ref PositionSet.empty in
      PositionSet.iter
        (fun v -> if v <> w then p := PositionSet.add (find v) !p)
        back_preds.(w);
      let q = ref !p in
      while not (PositionSet.is_empty !q) do
        let x = PositionSet.min_elt !q in
        q := PositionSet.remove x !q;
        PositionSet.iter
          (fun y ->
            let y = find y in
            if not (Dom.dominates w y) then failwith "irreducible graph"
            else if (not (PositionSet.mem y !p)) && y <> w then begin
              p := PositionSet.add y !p;
              q := PositionSet.add y !q
            end)
          non_back_preds.(x)
      done;
      PositionSet.iter
        (fun x ->
          header.(x) <- w;
          union x w)
        !p
    done
  let children = Array.make Dom.size PositionSet.empty
  let _ =
    for w = 0 to Dom.size - 1 do
      let header = header.(w) in
      children.(header) <- PositionSet.add w children.(header)
    done
  let loop_nodes = Iarray.of_array children
end
