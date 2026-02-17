open Normalize
module IntHashtbl = Hashtbl.Make (Int)

let rewrite_branch lookup_args instr =
  let changed = ref false in
  let go_use = function
    | Target.Label (((uid, _) as l), args) -> begin
      try
        let block_args = lookup_args uid in
        let args' =
          List.map
            (fun (a, b) -> if Target.is_tombstone a then a else b)
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

let hashtbl_size = 100

let deadcode graph =
  let fact = Construct.name_fact () in
  let block_args = IntHashtbl.create hashtbl_size in
  let first_in a = function
    | Cfg.Entry -> Flow.Dataflow a
    | Cfg.Label (((uid, _) as l), info) ->
      let args =
        List.map
          (fun arg -> if NameSet.mem arg a then arg else Name.tombstone)
          info.args
      in
      if args <> info.args then begin
        IntHashtbl.replace block_args uid
          (List.map (fun n -> Target.Reg n) args);
        Flow.Rewrite Cfg.(unfocus @@ label ~args l @@ focus_entry empty)
      end
      else Flow.Dataflow a
  in
  let handle_instruction instr a =
    NameSet.union (Target.uses instr) (NameSet.diff a (Target.defs instr))
  in
  let middle_in a (Cfg.Instruction instr) =
    if NameSet.(is_empty (inter (Target.defs instr) a)) then
      Flow.Rewrite Cfg.empty
    else Flow.Dataflow (handle_instruction instr a)
  in
  let calc_live_out = function
    | Cfg.Exit -> NameSet.empty
    | Cfg.Branch (instr, (uid, _)) -> handle_instruction instr (fact.get uid)
    | Cfg.CBranch (instr, (uid1, _), (uid2, _)) ->
      handle_instruction instr (NameSet.union (fact.get uid1) (fact.get uid2))
    | Cfg.Return instr -> handle_instruction instr NameSet.empty
  in
  let last_in _ last =
    match last with
    | Cfg.Exit -> Flow.Dataflow (calc_live_out last)
    | Cfg.Branch (i, l) ->
      let i, changed = rewrite_branch (IntHashtbl.find block_args) i in
      if changed then
        Flow.Rewrite Cfg.(unfocus ((First Entry, Last (Branch (i, l))), empty))
      else Flow.Dataflow (calc_live_out last)
    | Cfg.CBranch (i, l1, l2) ->
      let i, changed = rewrite_branch (IntHashtbl.find block_args) i in
      if changed then
        Flow.Rewrite
          Cfg.(unfocus ((First Entry, Last (CBranch (i, l1, l2))), empty))
      else Flow.Dataflow (calc_live_out last)
    | Cfg.Return _ -> Flow.Dataflow (calc_live_out last)
  in
  let pass = (fact, { Flow.BackwardPass.first_in; middle_in; last_in }) in
  snd @@ Flow.BackwardPass.solve_and_rewrite pass graph NameSet.empty
