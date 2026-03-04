module LabelSet = struct
  include CCSet.Make (Int)
  let pp = pp Format.pp_print_int
end
module LabelMap = struct
  include CCMap.Make (Int)
  let pp pp_v = pp Format.pp_print_int pp_v
end
module type S = sig
  val loop_headers : LabelSet.t
  val loop_nodes : LabelSet.t LabelMap.t
  val loop_nest_successors : LabelSet.t LabelMap.t
end
module Make
    (G : Graph.S)
    (Dom : Dominator.S with type label = G.label and type graph = G.graph) : S =
struct
  let loop_headers =
    let add_headers _uid block acc =
      let headers =
        G.(successors (last (unzip block)))
        |> List.filter (fun succ ->
            Dom.(
              dominates
                (position_of_label (Some succ))
                (position_of_label (G.block_label block))))
      in
      List.fold_left (fun acc (uid, _) -> LabelSet.add uid acc) acc headers
    in
    G.Blocks.fold add_headers Dom.graph LabelSet.empty

  let loop_nodes = LabelMap.empty

  let loop_nest_successors = LabelMap.empty
end
