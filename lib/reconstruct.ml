module IntMap = Map.Make (Int)
module IntHashtbl = Utils.IntHashtbl
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

  (* todo: cache reaching def for block *)
  let compute_reaching_def all_defs graph head =
    let rec go = function
      | G.First f ->
        let uid =
          match f with
          | G.Entry -> G.entry_uid
          | G.Label ((uid, _), _) -> uid
        in
        let defs =
          match f with
          | G.Entry -> Target.RegSet.empty
          | G.Label (_, info) ->
            Target.RegSet.(inter (of_list info.args) all_defs)
        in
        if Target.RegSet.is_empty defs then
          (* walk up dominator tree *)
          let parent =
            Dom.(G.idd (label_of_position (idom (position_of_uid uid))))
          in
          let head, _ = G.(goto_end (fst (focus parent graph))) in
          go head
        else (Target.RegSet.min_elt defs, Some uid)
      | G.Head (head, Instruction instr) ->
        let defs = Target.(RegSet.inter (defs instr) all_defs) in
        if Target.RegSet.is_empty defs then go head
        else (Target.RegSet.min_elt defs, None)
    in
    go head

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
    let all_defs = Target.RegSet.(union old_defs (union cloned_defs phis)) in
    let phi_worklist = ref PhiSet.empty in
    let blocks = G.reverse_postorder_dfs graph in
    let go_block graph block =
      let zblock = G.unzip block in
      let handle_instruction head instr =
        let go_use op =
          match Target.Reg.of_operand op with
          | Some reg when Target.RegSet.mem reg old_defs ->
            let reaching_def, is_phi =
              compute_reaching_def all_defs graph head
            in
            begin match is_phi with
            | Some phi_block_uid ->
              phi_worklist :=
                PhiSet.add (reaching_def, phi_block_uid) !phi_worklist
            | _ -> ()
            end;
            Target.Reg.to_operand reaching_def
          | _ -> op
        in
        Target.map_uses go_use instr
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
    let graph = List.fold_left go_block graph blocks in
    let rec phi_reaching_def phi_worklist graph =
      if PhiSet.is_empty phi_worklist then graph
      else
        let phi, phi_block_uid = PhiSet.min_elt phi_worklist in
        let phi_worklist = PhiSet.remove (phi, phi_block_uid) phi_worklist in
        let fold_pred (phi_worklist, graph) pred =
          let block, graph =
            G.(focus (idd (Dom.label_of_position pred)) graph)
          in
          let head, last = G.goto_end block in
          let reaching_def, is_phi = compute_reaching_def all_defs graph head in
          (* add reaching_def to last where phi arg is in phi_block_uid *)
          let args =
            match G.(first (fst (focus phi_block_uid graph))) with
            | G.Entry -> []
            | G.Label (_, info) -> info.args
          in
          let go_use op =
            match Target.destruct_label op with
            | Some (((uid, _) as l), ops)
              when uid = phi_block_uid && List.(length ops <> length args) ->
              Target.(label l (Reg.to_operand reaching_def :: ops))
            | _ -> op
          in
          let last =
            match last with
            | G.Exit -> G.Exit
            | G.Branch (i, l) -> G.Branch (Target.map_uses go_use i, l)
            | G.CBranch (i, l1, l2) ->
              G.CBranch (Target.map_uses go_use i, l1, l2)
            | G.Return i -> G.Return i
          in
          let graph = G.unfocus ((head, G.Last last), graph) in
          match is_phi with
          | Some block_uid ->
            (PhiSet.add (reaching_def, block_uid) phi_worklist, graph)
          | None -> (phi_worklist, graph)
        in
        let phi_worklist, graph =
          List.fold_left fold_pred (phi_worklist, graph)
            Dom.(predecessors (position_of_uid phi_block_uid))
        in
        phi_reaching_def phi_worklist graph
    in
    phi_reaching_def !phi_worklist graph
end
