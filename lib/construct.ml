module IntHashtbl = Hashtbl.Make (Int)

type liveness = {
  live_in : Normalize.Cfg.label -> Normalize.NameSet.t;
  live_out : Normalize.Cfg.label -> Normalize.NameSet.t;
}

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

let calc_a_orig graph : Normalize.Cfg.label -> Normalize.NameSet.t =
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
  fun (uid, _) -> fact.get uid

let calc_live graph =
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
    live_in = (fun (uid, _) -> liveness_fact.get uid);
    live_out =
      (fun (uid, _) ->
        calc_live_out @@ Normalize.Cfg.last @@ fst
        @@ Normalize.Cfg.focus uid graph);
  }
