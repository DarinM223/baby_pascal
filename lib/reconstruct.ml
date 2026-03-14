module IntMap = Map.Make (Int)
module Make
    (Target : Deadcode.Target)
    (G :
      module type of Graph.Make (Target))
        (Dom : Dominator.S with type label = G.label and type uid = G.uid) =
struct
  module RegSet = Set.Make (struct
    type t = G.Target.reg
    let compare = compare
  end)
  let reconstruct (fresh : unit -> G.Target.reg) (_old_defs : RegSet.t)
      (_cloned_defs : RegSet.t) (def_blocks : G.uid list) (graph : G.graph) :
      G.graph =
    (* for every block in dominance frontier, place a phi with fresh definition *)
    let df = Lazy.force Dom.dominator_frontier in
    let iter_df_bbs =
      List.concat_map
        (fun uid ->
          List.map
            (fun p -> G.idd (Dom.label_of_position p))
            (df (Dom.position_of_uid uid)))
        def_blocks
    in
    let place_phi (phis, graph) block =
      let phi_def = fresh () in
      let (head, tail), graph = G.focus block graph in
      let head =
        match head with
        | First Entry -> failwith "dominance frontier is entry"
        | First (Label (l, info)) ->
          G.First (Label (l, { info with args = phi_def :: info.args }))
        | _ -> failwith "zipper not at beginning of block"
      in
      (RegSet.add phi_def phis, G.unfocus ((head, tail), graph))
    in
    let _phis, _graph =
      List.fold_left place_phi (RegSet.empty, graph) iter_df_bbs
    in
    (* todo: build substitution map *)
    failwith "still learning to code"
end
