module IntHashtbl = Hashtbl.Make (Int)
module Name = Normalize.Name
module NameHashtbl = Hashtbl.Make (Name)
module IntMap = Graph_intf.IntMap
module IntSet = Graph_intf.IntSet
module Cfg = Normalize.Cfg
module NameSet = Normalize.NameSet
module Flow = Normalize.Flow
module Target = Normalize.Target

type liveness = {
  live_in : Cfg.uid -> NameSet.t;
  live_out : Cfg.uid -> NameSet.t;
}
type a_orig = Cfg.uid -> NameSet.t

let uid_of_label = function
  | None -> Cfg.entry_uid
  | Some (uid, _) -> uid

let name_fact () =
  let store = IntHashtbl.create 100 in
  {
    Flow.init_info = NameSet.empty;
    add_info = NameSet.union;
    changed = (fun ~before ~after -> NameSet.(cardinal after > cardinal before));
    get = IntHashtbl.find store;
    set = IntHashtbl.add store;
  }

let calc_a_orig graph : a_orig =
  let fact = name_fact () in
  let handle_instruction instr a =
    let { Target.defs; _ } = Target.info instr in
    NameSet.union a defs
  in
  let analysis =
    {
      Flow.BackwardAnalysis.first_in = (fun a _ -> a);
      middle_in = (fun a (Instruction instr) -> handle_instruction instr a);
      last_in = (fun _ -> NameSet.empty);
    }
  in
  let analysis = (fact, analysis) in
  let _ = Flow.BackwardAnalysis.run analysis graph in
  fact.get

let calc_live graph : liveness =
  let liveness_fact = name_fact () in
  let handle_instruction instr a =
    let { Target.uses; defs } = Target.info instr in
    NameSet.union uses (NameSet.diff a defs)
  in
  let calc_live_out = function
    | Cfg.Exit -> NameSet.empty
    | Cfg.Branch (_, (uid, _)) -> liveness_fact.get uid
    | Cfg.CBranch (instr, (uid1, _), (uid2, _)) ->
      handle_instruction instr
      @@ NameSet.union (liveness_fact.get uid1) (liveness_fact.get uid2)
    | Cfg.Return (instr, _) -> handle_instruction instr NameSet.empty
  in
  let liveness_analysis =
    {
      Flow.BackwardAnalysis.first_in = (fun a _ -> a);
      middle_in = (fun a (Instruction instr) -> handle_instruction instr a);
      last_in = calc_live_out;
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
  IntMap.iter
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
