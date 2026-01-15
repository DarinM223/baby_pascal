module IntHashtbl = Hashtbl.Make (Int)
module NameHashtbl = Hashtbl.Make (Normalize.Name)
module IntMap = Graph_intf.IntMap
module IntSet = Graph_intf.IntSet

type liveness = {
  live_in : Normalize.Cfg.uid -> Normalize.NameSet.t;
  live_out : Normalize.Cfg.uid -> Normalize.NameSet.t;
}
type a_orig = Normalize.Cfg.uid -> Normalize.NameSet.t

let uid_of_label = function
  | None -> Normalize.Cfg.entry_uid
  | Some (uid, _) -> uid

let name_fact () =
  let open Normalize in
  let store = IntHashtbl.create 100 in
  {
    Flow.init_info = NameSet.empty;
    add_info = NameSet.union;
    changed = (fun ~before ~after -> NameSet.(cardinal after > cardinal before));
    get = IntHashtbl.find store;
    set = IntHashtbl.add store;
  }

let calc_a_orig graph : a_orig =
  let open Normalize in
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
  let open Normalize in
  let liveness_fact = name_fact () in
  let handle_instruction instr a =
    let { Target.uses; defs } = Target.info instr in
    NameSet.union uses (NameSet.diff a defs)
  in
  let calc_live_out = function
    | Normalize.Cfg.Exit -> NameSet.empty
    | Normalize.Cfg.Branch (_, (uid, _)) -> liveness_fact.get uid
    | Normalize.Cfg.CBranch (instr, (uid1, _), (uid2, _)) ->
      handle_instruction instr
      @@ NameSet.union (liveness_fact.get uid1) (liveness_fact.get uid2)
    | Normalize.Cfg.Return (instr, _) -> handle_instruction instr NameSet.empty
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
      (fun uid ->
        calc_live_out @@ Normalize.Cfg.last @@ fst
        @@ Normalize.Cfg.focus uid graph);
  }

let insert_phis (test : Normalize.Cfg.uid -> Normalize.Name.t -> bool)
    (module Dom : Dominator.S with type label = Normalize.Cfg.label)
    (a_orig : a_orig) (graph : Normalize.Cfg.graph) =
  let open Normalize in
  let defsites : Normalize.Cfg.uid NameHashtbl.t = NameHashtbl.create 100 in
  IntMap.iter
    (fun n _ -> NameSet.iter (fun a -> NameHashtbl.add defsites a n) (a_orig n))
    graph;
  let a_phi = Hashtbl.create (NameHashtbl.length defsites) in
  let go_variable a _ graph =
    let w = ref (IntSet.of_list (NameHashtbl.find_all defsites a)) in
    while not (IntSet.is_empty !w) do
      let n = IntSet.min_elt !w in
      let l = Normalize.Cfg.(block_label (zip (fst (focus n graph)))) in
      w := IntSet.remove n !w;
      let df =
        l |> Dom.position_of_label
        |> Lazy.force Dom.dominator_frontier
        |> List.map (Fun.compose uid_of_label Dom.label_of_position)
      in
      List.iter
        (fun y ->
          if (not (List.mem y (Hashtbl.find_all a_phi a))) && test y a then begin
            let _node = IntMap.find y graph in
            (* let phi = List.init (IntSet.cardinal node.Block.pred) (fun _ -> a) in
            CCVector.push node.phis { r = a'; ins = phi }; *)
            Hashtbl.add a_phi a y;
            if not (NameSet.mem a (a_orig y)) then w := IntSet.add y !w
          end)
        df
    done;
    graph
  in
  NameHashtbl.fold go_variable defsites graph
