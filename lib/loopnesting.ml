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
  val loop_nodes : LabelSet.t LabelMap.t Lazy.t
  val loop_nest_successors : LabelSet.t LabelMap.t Lazy.t
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

  let add_label k v =
    LabelMap.update (G.idd k) (function
      | None -> Some (LabelSet.singleton (G.idd v))
      | Some s -> Some (LabelSet.add (G.idd v) s))

  let loop_nodes, loop_nest_successors =
    let rec dfs acc block = function
      | top :: stack ->
        let children =
          Lazy.force Dom.dominator_tree_at (Dom.position_of_label block)
          |> Dom.tree_children |> List.map Dom.tree_label
        in
        let go_child (loop_nodes, loop_nest_successors) child =
          let succs =
            G.(successors (last (fst (focus (idd child) Dom.graph))))
            |> List.map (fun l -> Some l)
          in
          if LabelSet.mem (G.idd child) loop_headers then
            let loop_nest_successors =
              add_label top child loop_nest_successors
            in
            dfs (loop_nodes, loop_nest_successors) child (child :: top :: stack)
          else if List.mem top succs then
            let loop_nodes = add_label top child loop_nodes in
            dfs (loop_nodes, loop_nest_successors) child stack
          else
            let loop_nodes = add_label top child loop_nodes in
            dfs (loop_nodes, loop_nest_successors) child (top :: stack)
        in
        List.fold_left go_child acc children
      | [] -> failwith "loop nodes: no top of stack"
    in
    let result = lazy (dfs (LabelMap.empty, LabelMap.empty) None [ None ]) in
    (Lazy.map fst result, Lazy.map snd result)
end
