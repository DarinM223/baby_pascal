open Normalize
module IntHashtbl = Hashtbl.Make (Int)
module NameHashtbl = Hashtbl.Make (struct
  include Name
  let equal n1 n2 = label n1 = label n2
  let hash n = Hashtbl.hash (label n)
end)
module IntSet = Graph_intf.IntSet

type liveness = {
  live_in : Cfg.uid -> NameSet.t;
  live_out : Cfg.uid -> NameSet.t;
}
type a_orig = Cfg.uid -> NameSet.t

let uid_of_label = function
  | None -> Cfg.entry_uid
  | Some (uid, _) -> uid

let hashtbl_size = 100

let name_fact () =
  let store = IntHashtbl.create hashtbl_size in
  {
    Flow.init_info = NameSet.empty;
    add_info = NameSet.union;
    changed = (fun ~before ~after -> NameSet.(cardinal after > cardinal before));
    skip_block = Fun.const false;
    get = IntHashtbl.find store;
    set = IntHashtbl.replace store;
  }

let calc_a_orig graph : a_orig =
  let fact = name_fact () in
  let handle_instruction instr a = NameSet.union a (Target.defs instr) in
  let analysis =
    {
      Flow.BackwardAnalysis.first_in = (fun a _ -> a);
      middle_in = (fun a (Instruction instr) -> handle_instruction instr a);
      last_in = (fun _ _ -> NameSet.empty);
    }
  in
  let analysis = (fact, analysis) in
  let _ = Flow.BackwardAnalysis.run analysis graph in
  fact.get

let calc_live graph : liveness =
  let liveness_fact = name_fact () in
  let handle_instruction instr a =
    NameSet.union (Target.uses instr) (NameSet.diff a (Target.defs instr))
  in
  let calc_live_out = function
    | Cfg.Exit -> NameSet.empty
    | Cfg.Branch (_, (uid, _)) -> liveness_fact.get uid
    | Cfg.CBranch (instr, (uid1, _), (uid2, _)) ->
      handle_instruction instr
      @@ NameSet.union (liveness_fact.get uid1) (liveness_fact.get uid2)
    | Cfg.Return instr -> handle_instruction instr NameSet.empty
  in
  let liveness_analysis =
    {
      Flow.BackwardAnalysis.first_in = (fun a _ -> a);
      middle_in = (fun a (Instruction instr) -> handle_instruction instr a);
      last_in = Fun.const calc_live_out;
    }
  in
  let liveness_analysis = (liveness_fact, liveness_analysis) in
  let _ = Flow.BackwardAnalysis.run liveness_analysis graph in
  {
    live_in = liveness_fact.get;
    live_out =
      (fun uid -> calc_live_out @@ Cfg.last @@ fst @@ Cfg.focus uid graph);
  }

let insert_phis (test : Cfg.uid -> Name.t -> bool)
    (module Dom : Dominator.S with type label = Cfg.label) (a_orig : a_orig)
    (graph : Cfg.graph) =
  let defsites : Cfg.uid NameHashtbl.t = NameHashtbl.create 100 in
  Cfg.Blocks.iter
    (fun n _ -> NameSet.iter (fun a -> NameHashtbl.add defsites a n) (a_orig n))
    graph;
  let a_phi = NameHashtbl.(create (length defsites)) in
  let go_variable a _ graph =
    let go_frontier_node (worklist, graph) node_id =
      if
        (not (List.mem node_id (NameHashtbl.find_all a_phi a)))
        && test node_id a
      then begin
        let zblock, graph = Cfg.focus node_id graph in
        let graph =
          match Cfg.goto_start zblock with
          | Cfg.Entry, _ -> failwith "Cannot add phi to entry block"
          | Cfg.Label (l, i), tail ->
            let zblock =
              (Cfg.(First (Label (l, { i with args = a :: i.args }))), tail)
            in
            Cfg.unfocus (zblock, graph)
        in
        NameHashtbl.add a_phi a node_id;
        let worklist =
          if not (NameSet.mem a (a_orig node_id)) then
            IntSet.add node_id worklist
          else worklist
        in
        (worklist, graph)
      end
      else (worklist, graph)
    in
    let rec go_defsite worklist graph =
      if IntSet.is_empty worklist then graph
      else
        let n = IntSet.min_elt worklist in
        let worklist = IntSet.remove n worklist in
        let l = Cfg.(block_label (zip (fst (focus n graph)))) in
        let df =
          l |> Dom.position_of_label
          |> Lazy.force Dom.dominator_frontier
          |> List.map (Fun.compose uid_of_label Dom.label_of_position)
        in
        let worklist, graph =
          List.fold_left go_frontier_node (worklist, graph) df
        in
        go_defsite worklist graph
    in
    go_defsite (IntSet.of_list (NameHashtbl.find_all defsites a)) graph
  in
  NameHashtbl.fold go_variable defsites graph

let insert_phis_minimal = insert_phis (fun _ _ -> true)

let insert_phis_pruned (live : liveness) =
  insert_phis (fun y a -> NameSet.mem a (live.live_in y))

let rename_variables (module Dom : Dominator.S with type label = Cfg.label)
    graph =
  let ( let* ) = ( @@ ) in
  let count = NameHashtbl.create hashtbl_size in
  let stack = NameHashtbl.create hashtbl_size in
  let rec rename graph label children k =
    let zblock, graph =
      match label with
      | None -> Cfg.focus_entry graph
      | Some (uid, _) -> Cfg.focus uid graph
    in
    let first, tail = Cfg.goto_start zblock in
    let replace_use (use : Name.t) : Name.t =
      let i = try NameHashtbl.find stack use with Not_found -> 0 in
      Name.update_index i use
    in
    let replace_def (def : Name.t) : Name.t =
      begin try NameHashtbl.replace count def (NameHashtbl.find count def + 1)
      with Not_found -> NameHashtbl.add count def 1
      end;
      let i = NameHashtbl.find count def in
      NameHashtbl.add stack def i;
      Name.update_index i def
    in
    let rename_block_argument vardefs (def : Name.t) =
      (NameSet.add def vardefs, replace_def def)
    in
    let rename_instruction vardefs (instr : Target.instr) =
      let instr =
        Target.map_uses
          (function
            | Reg reg -> Reg (replace_use reg)
            (* ignore global labels *)
            | Label (((-1, _) as l), args) -> Label (l, args)
            | Label (((uid, _) as l), args) -> begin
              let first =
                if Some l = label then first
                else Cfg.first @@ fst @@ Cfg.focus uid graph
              in
              match first with
              | Cfg.Entry -> Label (l, args)
              | Cfg.Label (_, args') ->
                (* handle call instructions to pass block parameters *)
                Label
                  (l, List.map (fun n -> Target.Reg (replace_use n)) args'.args)
            end
            | op -> op)
          instr
      in
      let vardefs = ref vardefs in
      let instr =
        Target.map_defs
          (function
            | Reg reg ->
              vardefs := NameSet.add reg !vardefs;
              Reg (replace_def reg)
            | op -> op)
          instr
      in
      (!vardefs, instr)
    in
    let rename_last vardefs = function
      | Cfg.Exit -> (vardefs, Cfg.Exit)
      | Cfg.Branch (instr, label) ->
        let vardefs, instr = rename_instruction vardefs instr in
        (vardefs, Cfg.Branch (instr, label))
      | Cfg.CBranch (instr, l1, l2) ->
        let vardefs, instr = rename_instruction vardefs instr in
        (vardefs, Cfg.CBranch (instr, l1, l2))
      | Cfg.Return instr ->
        let vardefs, instr = rename_instruction vardefs instr in
        (vardefs, Cfg.Return instr)
    in
    let vardefs, first =
      match first with
      | Cfg.Entry -> (NameSet.empty, first)
      | Cfg.Label (l, args) ->
        let vardefs, args' =
          List.fold_right
            (fun arg (vardefs, args) ->
              let vardefs, arg = rename_block_argument vardefs arg in
              (vardefs, arg :: args))
            args.args (NameSet.empty, [])
        in
        (vardefs, Cfg.Label (l, { args with args = args' }))
    in
    let rec go_tail vardefs tail k =
      match tail with
      | Cfg.Tail (Cfg.Instruction instr, rest) ->
        let vardefs, instr = rename_instruction vardefs instr in
        let* vardefs, rest = go_tail vardefs rest in
        k (vardefs, Cfg.Tail (Cfg.Instruction instr, rest))
      | Cfg.Last l ->
        let vardefs, l = rename_last vardefs l in
        k (vardefs, Cfg.Last l)
    in
    let* vardefs, tail = go_tail vardefs tail in
    let graph = Cfg.unfocus ((Cfg.First first, tail), graph) in
    let rec go_children graph children k =
      match children with
      | child :: rest ->
        let* graph = walk graph child in
        go_children graph rest k
      | [] -> k graph
    in
    let* graph = go_children graph children in
    NameSet.iter (NameHashtbl.remove stack) vardefs;
    k graph
  and walk graph tree k =
    match tree with
    | Dom.Node (_, l, children) -> rename graph l children k
    | Dom.Leaf (_, l) -> rename graph l [] k
  in
  walk graph (Lazy.force Dom.dominator_tree) (fun a -> a)
