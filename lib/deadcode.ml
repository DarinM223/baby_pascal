module Cfg = Normalize.Cfg
module Name = Normalize.Name
module NameSet = Normalize.NameSet
module Flow = Normalize.Flow
module Target = Normalize.Target
module IntHashtbl = Hashtbl.Make (Int)

let hashtbl_size = 100

let deadcode graph =
  let liveness_fact = Construct.name_fact () in
  let block_args = IntHashtbl.create hashtbl_size in
  let handle_instruction instr a =
    NameSet.union (Target.uses instr) (NameSet.diff a (Target.defs instr))
  in
  let handle_first a = function
    | Cfg.Entry -> Flow.Dataflow a
    | Cfg.Label (((uid, _) as l), info) ->
      let args =
        List.map
          (fun arg -> if NameSet.mem arg a then arg else Name.tombstone)
          info.args
      in
      if args <> info.args then begin
        IntHashtbl.replace block_args uid args;
        Flow.Rewrite Cfg.(unfocus @@ label ~args l @@ focus_entry empty)
      end
      else Flow.Dataflow a
  in
  let handle_middle a (Cfg.Instruction instr) =
    if NameSet.(is_empty (inter (Target.defs instr) a)) then
      Flow.Rewrite Cfg.empty
    else Flow.Dataflow (handle_instruction instr a)
  in
  let calc_live_out = function
    | Cfg.Exit -> NameSet.empty
    | Cfg.Branch (instr, (uid, _)) ->
      handle_instruction instr @@ liveness_fact.get uid
    | Cfg.CBranch (instr, (uid1, _), (uid2, _)) ->
      handle_instruction instr
      @@ NameSet.union (liveness_fact.get uid1) (liveness_fact.get uid2)
    | Cfg.Return (instr, _) -> handle_instruction instr NameSet.empty
  in
  let rewrite_branch instr =
    let changed = ref false in
    let go_use = function
      | Target.Label (((uid, _) as l), args) -> begin
        try
          let block_args = IntHashtbl.find block_args uid in
          let args' =
            List.map
              (fun (a, b) -> if Name.is_tombstone a then a else b)
              (List.combine block_args args)
          in
          if args' <> args then changed := true;
          Target.Label (l, args')
        with Not_found -> Target.Label (l, args)
      end
      | op -> op
    in
    let instr = Target.map_uses go_use instr in
    (instr, !changed)
  in
  let handle_last last =
    match last with
    | Cfg.Exit -> Flow.Dataflow (calc_live_out last)
    | Cfg.Branch (i, l) ->
      let i, changed = rewrite_branch i in
      if changed then
        Flow.Rewrite Cfg.(unfocus ((First Entry, Last (Branch (i, l))), empty))
      else Flow.Dataflow (calc_live_out last)
    | Cfg.CBranch (i, l1, l2) ->
      let i, changed = rewrite_branch i in
      if changed then
        Flow.Rewrite
          Cfg.(unfocus ((First Entry, Last (CBranch (i, l1, l2))), empty))
      else Flow.Dataflow (calc_live_out last)
    | Cfg.Return (_, _) -> Flow.Dataflow (calc_live_out last)
  in
  let pass =
    {
      Flow.BackwardPass.first_in = handle_first;
      middle_in = handle_middle;
      last_in = handle_last;
    }
  in
  let pass = (liveness_fact, pass) in
  snd @@ Flow.BackwardPass.solve_and_rewrite pass graph NameSet.empty
