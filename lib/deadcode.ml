module Cfg = Normalize.Cfg
module NameSet = Normalize.NameSet
module Flow = Normalize.Flow
module Target = Normalize.Target

let deadcode graph =
  let liveness_fact = Construct.name_fact () in
  let handle_instruction instr a =
    NameSet.union (Target.uses instr) (NameSet.diff a (Target.defs instr))
  in
  let handle_middle instr a =
    if NameSet.(is_empty (inter (Target.defs instr) a)) then
      Flow.Rewrite Cfg.empty
    else Flow.Dataflow (handle_instruction instr a)
  in
  let calc_live_out = function
    | Cfg.Exit -> NameSet.empty
    | Cfg.Branch (_, (uid, _)) -> liveness_fact.get uid
    | Cfg.CBranch (instr, (uid1, _), (uid2, _)) ->
      handle_instruction instr
      @@ NameSet.union (liveness_fact.get uid1) (liveness_fact.get uid2)
    | Cfg.Return (instr, _) -> handle_instruction instr NameSet.empty
  in
  let pass =
    {
      Flow.BackwardPass.first_in = (fun a _ -> Dataflow a);
      middle_in = (fun a (Instruction instr) -> handle_middle instr a);
      last_in = (fun l -> Dataflow (calc_live_out l));
    }
  in
  let pass = (liveness_fact, pass) in
  snd @@ Flow.BackwardPass.solve_and_rewrite pass graph NameSet.empty
