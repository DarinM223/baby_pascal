module IntHashtbl = Utils.IntHashtbl

module type Target = sig
  include Graph.Target with type label = int * string
  include
    Instruction.Target
      with type label := label
       and type instr := instr
       and type operand := operand
  module Reg : sig
    type t = reg
    val tombstone : t
    val of_operand : operand -> t option
    val to_operand : t -> operand
  end
  module RegSet : Set.S with type elt = reg
  val uses : instr -> RegSet.t
  val defs : instr -> RegSet.t
  val is_side_effectful : instr -> bool
end

module Make
    (Target : Target)
    (G :
      module type of Graph.Make (Target))
        (Flow : Dataflow.S with module G = G) =
struct
  let hashtbl_size = 100
  let fact () =
    let store = IntHashtbl.create hashtbl_size in
    {
      Flow.init_info = Target.RegSet.empty;
      add_info = Target.RegSet.union;
      changed =
        (fun ~before ~after -> Target.RegSet.(cardinal after > cardinal before));
      skip_block = Fun.const false;
      get = IntHashtbl.find store;
      set = IntHashtbl.replace store;
    }

  let rewrite_branch lookup_args instr =
    let changed = ref false in
    let go_use operand =
      match Target.destruct_label operand with
      | Some (((uid, _) as l), args) ->
        begin try
          let block_args = lookup_args uid in
          let args' =
            List.map
              (fun (a, b) -> if Target.is_tombstone a then a else b)
              (List.combine block_args args)
          in
          if args' <> args then changed := true;
          Target.label l args'
        with Not_found -> Target.label l args
        end
      | _ -> operand
    in
    let instr = Target.map_uses go_use instr in
    (instr, !changed)

  let hashtbl_size = 100

  let deadcode graph =
    let fact = fact () in
    let block_args = IntHashtbl.create hashtbl_size in
    let first_in a = function
      | G.Entry -> Flow.Dataflow a
      | G.Label (((uid, _) as l), info) ->
        let args =
          List.map
            (fun arg ->
              if Target.RegSet.mem arg a then arg else Target.Reg.tombstone)
            info.args
        in
        if args <> info.args then begin
          IntHashtbl.replace block_args uid
            (List.map Target.Reg.to_operand args);
          Flow.Rewrite G.(unfocus @@ label ~args l @@ focus_entry empty)
        end
        else Flow.Dataflow a
    in
    let handle_instruction instr a =
      Target.RegSet.union (Target.uses instr)
        (Target.RegSet.diff a (Target.defs instr))
    in
    let middle_in a (G.Instruction instr) =
      if
        Target.RegSet.(is_empty (inter (Target.defs instr) a))
        && not (Target.is_side_effectful instr)
      then Flow.Rewrite G.empty
      else Flow.Dataflow (handle_instruction instr a)
    in
    let calc_live_out = function
      | G.Exit -> Target.RegSet.empty
      | G.Branch (instr, (uid, _)) -> handle_instruction instr (fact.get uid)
      | G.CBranch (instr, (uid1, _), (uid2, _)) ->
        handle_instruction instr
          (Target.RegSet.union (fact.get uid1) (fact.get uid2))
      | G.Return instr -> handle_instruction instr Target.RegSet.empty
    in
    let last_in _ last =
      match last with
      | G.Exit -> Flow.Dataflow (calc_live_out last)
      | G.Branch (i, l) ->
        let i, changed = rewrite_branch (IntHashtbl.find block_args) i in
        if changed then
          Flow.Rewrite G.(unfocus ((First Entry, Last (Branch (i, l))), empty))
        else Flow.Dataflow (calc_live_out last)
      | G.CBranch (i, l1, l2) ->
        let i, changed = rewrite_branch (IntHashtbl.find block_args) i in
        if changed then
          Flow.Rewrite
            G.(unfocus ((First Entry, Last (CBranch (i, l1, l2))), empty))
        else Flow.Dataflow (calc_live_out last)
      | G.Return _ -> Flow.Dataflow (calc_live_out last)
    in
    let pass = (fact, { Flow.BackwardPass.first_in; middle_in; last_in }) in
    snd @@ Flow.BackwardPass.solve_and_rewrite pass graph Target.RegSet.empty
end

module M = Make (Normalize.Target) (Normalize.Cfg) (Normalize.Flow)
