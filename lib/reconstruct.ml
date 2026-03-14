module IntMap = Map.Make (Int)
module IntHashtbl = Hashtbl.Make (Int)
let hashtbl_size = 100

module Make
    (Target : Deadcode.Target)
    (G :
      module type of Graph.Make (Target))
        (Dom : Dominator.S with type label = G.label and type uid = G.uid) =
struct
  module PhiSet = Set.Make (struct
    type t = G.Target.reg * G.uid
    let compare = compare
  end)

  let compute_reaching_def =
    (* cache reaching def for block *)
    let _def_cache = Array.make Dom.size None in
    failwith ""

  let reconstruct (fresh : unit -> G.Target.reg) (old_defs : Target.RegSet.t)
      (cloned_defs : Target.RegSet.t) (def_blocks : G.uid list)
      (graph : G.graph) : G.graph =
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
      (Target.RegSet.add phi_def phis, G.unfocus ((head, tail), graph))
    in
    let phis, graph =
      List.fold_left place_phi (Target.RegSet.empty, graph) iter_df_bbs
    in
    let _all_defs = Target.RegSet.(union old_defs (union cloned_defs phis)) in
    let _phi_worklist = PhiSet.empty in
    let blocks = G.reverse_postorder_dfs graph in
    let go_block graph block =
      (* todo: go over instructions in block,
         if instruction has use in old_defs, compute reaching def *)
      let zblock = G.unzip block in
      let handle_instruction _head instr =
        let _defs = Target.RegSet.inter (Target.uses instr) old_defs in
        failwith ""
      in
      let rec go = function
        | head, G.Tail (Instruction i, t) ->
          go (G.Head (head, Instruction (handle_instruction head i)), t)
        | head, G.Last l ->
          let l =
            match l with
            | G.Exit -> G.Exit
            | G.Branch (i, l) -> G.Branch (handle_instruction head i, l)
            | G.CBranch (i, l1, l2) ->
              G.CBranch (handle_instruction head i, l1, l2)
            | G.Return i -> G.Return (handle_instruction head i)
          in
          (head, G.Last l)
      in
      let zblock = go zblock in
      G.unfocus (zblock, graph)
    in
    let _graph = List.fold_left go_block graph blocks in
    failwith "still learning to code"
end
