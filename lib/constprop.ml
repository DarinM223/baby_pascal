open Normalize
module IntHashtbl = Hashtbl.Make (Int)
module NameMap = struct
  include CCMap.Make (struct
    include Name
    let compare = compare
  end)
  let pp pp_v = pp Name.pp pp_v
end
module OperandSet = struct
  include CCSet.Make (struct
    type t = Cfg.uid * Target.operand
    let compare = compare
  end)
  let pp_tuple fmt (uid, op) =
    Format.fprintf fmt "(%d,%a)" uid Target.pp_operand op
  let pp = pp pp_tuple
end

let hashtbl_size = 100

let block_args_fact () =
  let store = IntHashtbl.create hashtbl_size in
  {
    Flow.init_info = NameMap.empty;
    add_info = NameMap.union (fun _ a b -> Some (OperandSet.union a b));
    changed =
      (fun ~before ~after -> not (NameMap.equal OperandSet.equal before after));
    skip_block = Fun.const false;
    get = IntHashtbl.find store;
    set = IntHashtbl.add store;
  }

let block_args graph =
  let fact = block_args_fact () in
  let args_tbl = IntHashtbl.create hashtbl_size in
  let first_in a = function
    | Cfg.Entry -> a
    | Cfg.Label ((uid, _), info) ->
      IntHashtbl.replace args_tbl uid info.args;
      List.fold_left
        (fun a arg ->
          NameMap.update arg
            (function
              | None -> Some OperandSet.empty
              | Some a -> Some a)
            a)
        a info.args
  in
  let last_in uid =
    let go_use (a : OperandSet.t NameMap.t) = function
      | Target.Label ((uid', _), args) -> begin
        try
          let args' = IntHashtbl.find args_tbl uid' in
          List.fold_left
            (fun a (arg', arg) ->
              NameMap.update arg'
                (function
                  | None -> Some (OperandSet.singleton (uid, arg))
                  | Some set -> Some (OperandSet.add (uid, arg) set))
                a)
            a (List.combine args' args)
        with Not_found -> a
      end
      | _ -> a
    in
    function
    | Cfg.Exit -> NameMap.empty
    | Cfg.Branch (i, (uid, _)) ->
      List.fold_left go_use (fact.get uid) (Target.srcs i)
    | Cfg.CBranch (i, (uid1, _), (uid2, _)) ->
      List.fold_left go_use
        (fact.add_info (fact.get uid1) (fact.get uid2))
        (Target.srcs i)
    | Cfg.Return _ -> NameMap.empty
  in
  let analysis =
    { Flow.BackwardAnalysis.first_in; middle_in = (fun a _ -> a); last_in }
  in
  let analysis = (fact, analysis) in
  let _ = Flow.BackwardAnalysis.run analysis graph in
  fact.get Cfg.entry_uid

type lattice =
  | NeverDefined
  | Defined of int
  | OverDefined
[@@deriving show, eq]

type t = {
  mapping : lattice NameMap.t;
  args : Target.regs;
  executable : bool;
}
[@@deriving show, eq]

let state_fact () =
  let store = IntHashtbl.create hashtbl_size in
  {
    Flow.init_info = { mapping = NameMap.empty; args = []; executable = false };
    add_info =
      (fun a b ->
        {
          mapping = NameMap.union (fun _ a _ -> Some a) a.mapping b.mapping;
          args = a.args;
          executable = a.executable || b.executable;
        });
    changed = (fun ~before ~after -> not (equal before after));
    skip_block =
      (fun uid ->
        uid <> Cfg.entry_uid && not (IntHashtbl.find store uid).executable);
    get = IntHashtbl.find store;
    set = IntHashtbl.add store;
  }

let rec remove_consecutive_duplicates = function
  | [] -> []
  | [ a ] -> [ a ]
  | a :: b :: rest ->
    if a = b then remove_consecutive_duplicates (b :: rest)
    else a :: remove_consecutive_duplicates (b :: rest)

let apply_uop arg = function
  | Ast.Not -> if arg <> 0 then 0 else 1

let apply_bop l r = function
  | Ast.Add -> l + r
  | Ast.Sub -> l - r
  | Ast.Mul -> l * r
  | Ast.And -> Int.logand l r
  | Ast.Or -> Int.logor l r
  | Ast.Eq -> if l = r then 1 else 0
  | Ast.Neq -> if l = r then 0 else 1
  | Ast.Lt -> if l < r then 1 else 0
  | Ast.Le -> if l <= r then 1 else 0
  | Ast.Gt -> if l > r then 1 else 0
  | Ast.Ge -> if l >= r then 1 else 0

let apply_cond l r = function
  | Target.LT -> l < r
  | Target.LE -> l <= r
  | Target.GT -> l > r
  | Target.GE -> l >= r
  | Target.EQ -> l = r
  | Target.NE -> l <> r

let rewrite_uses lookup_operand a instr =
  let handle_operand op =
    match lookup_operand a op with
    | Defined c -> Target.Const c
    | _ -> op
  in
  let instr' =
    Target.map_uses
      (function
        | Label (l, args) -> Label (l, List.map handle_operand args)
        | (Const _ | Reg _) as op -> handle_operand op)
      instr
  in
  (instr', not (Target.equal_instr instr' instr))

let fold_conditional = function
  | Cfg.CBranch
      (Target.Cbranch (Const i, Const j, op, l1, l1args, l2, l2args), l1', l2')
    ->
    if apply_cond i j op then Cfg.Branch (Target.Goto (l1, l1args), l1')
    else Cfg.Branch (Target.Goto (l2, l2args), l2')
  | i -> i

let is_side_effectful = function
  | Target.(Call _ | Return _) -> true
  | _ -> false

let constprop (block_args : OperandSet.t NameMap.t) graph =
  let fact = state_fact () in
  let converged = ref false in
  let lookup_operand a = function
    | Target.Const c -> Defined c
    | Target.Reg r ->
      (try NameMap.find r a.mapping with Not_found -> NeverDefined)
    | _ -> NeverDefined
  in
  let add_mapping a res res_value =
    match res_value with
    | Some v -> { a with mapping = NameMap.add res v a.mapping }
    | None -> a
  in
  let first_out = function
    | Cfg.Entry -> Flow.Dataflow fact.init_info
    | Cfg.Label (((uid, _) as l), info) ->
      let a = fact.get uid in
      let update_block_arg a arg =
        let call_args = NameMap.find arg block_args in
        let get_values acc = function
          | uid, Target.Const i when (fact.get uid).executable ->
            Defined i :: acc
          | uid, Target.Reg arg when (fact.get uid).executable -> begin
            match NameMap.find_opt arg a.mapping with
            | Some NeverDefined | None -> acc
            | Some v -> v :: acc
          end
          | _ -> acc
        in
        let values =
          call_args |> OperandSet.to_list |> List.fold_left get_values []
        in
        add_mapping a arg
          (match remove_consecutive_duplicates values with
          | [ v ] -> Some v
          | [] -> None
          | _ -> Some OverDefined)
      in
      if not !converged then
        let a = List.fold_left update_block_arg a info.args in
        let rewrite_block_arg arg =
          match NameMap.find_opt arg a.mapping with
          | Some (Defined _) -> Name.tombstone
          | _ -> arg
        in
        let args = List.map rewrite_block_arg info.args in
        Flow.Dataflow { a with args }
      else if a.args = info.args then Flow.Dataflow a
      else
        Flow.Rewrite Cfg.(unfocus @@ label ~args:a.args l @@ focus_entry empty)
  in
  let handle_instruction a = function
    | Target.Assign (Reg res, arg) ->
      add_mapping a res
        (match lookup_operand a arg with
        | OverDefined -> Some OverDefined
        | NeverDefined -> None
        | Defined arg -> Some (Defined arg))
    | Target.Assign _ ->
      failwith "handle_instruction: assign destination not a name"
    | Target.Uop (Reg res, uop, arg) ->
      add_mapping a res
        (match lookup_operand a arg with
        | OverDefined -> Some OverDefined
        | NeverDefined -> None
        | Defined arg -> Some (Defined (apply_uop arg uop)))
    | Target.Uop _ -> failwith "handle_instruction: uop destination not a name"
    | Target.Bop (Reg res, bop, lhs, rhs) ->
      add_mapping a res
        (match (lookup_operand a lhs, lookup_operand a rhs) with
        | OverDefined, _ | _, OverDefined -> Some OverDefined
        | NeverDefined, _ | _, NeverDefined -> None
        | Defined l, Defined r -> Some (Defined (apply_bop l r bop)))
    | Target.Bop _ -> failwith "handle_instruction: bop destination not a name"
    | Target.Call (Reg r, _, _) ->
      { a with mapping = NameMap.add r OverDefined a.mapping }
    | Target.Call _ ->
      failwith "handle_instruction: call destination not a name"
    | Target.Return _ -> a
    | Target.Goto _ ->
      failwith "handle_instruction: goto instruction unexpected"
    | Target.Cbranch _ ->
      failwith "handle_instruction: cbranch instruction unexpected"
  in
  let middle_out a (Cfg.Instruction instr) =
    let all_defs_defined () =
      instr |> Target.defs |> NameSet.to_list
      |> List.map (fun n -> lookup_operand a (Reg n))
      |> List.for_all (function
        | Defined _ -> true
        | _ -> false)
    in
    if not !converged then Flow.Dataflow (handle_instruction a instr)
    else if all_defs_defined () && not (is_side_effectful instr) then
      Flow.Rewrite Cfg.empty
    else
      let instr, changed = rewrite_uses lookup_operand a instr in
      if changed then
        Flow.Rewrite Cfg.(unfocus @@ instruction instr @@ focus_entry empty)
      else Flow.Dataflow a
  in
  let get_args uid = List.map (fun n -> Target.Reg n) (fact.get uid).args in
  let last_outs self_uid a = function
    | Cfg.Exit -> Flow.Dataflow (fun set -> set self_uid a)
    | Cfg.Branch (i, ((uid, _) as l)) ->
      if not !converged then
        Flow.Dataflow
          (fun set ->
            set self_uid a;
            set uid { a with executable = true })
      else
        let i, changed = Deadcode.rewrite_branch get_args i in
        let i, changed' = rewrite_uses lookup_operand a i in
        if changed || changed' then
          Flow.Rewrite
            Cfg.(unfocus ((First Entry, Last (Branch (i, l))), empty))
        else Flow.Dataflow (fun _ -> ())
    | Cfg.CBranch
        ( (Target.Cbranch (lhs, rhs, cond, _, _, _, _) as i),
          ((uid1, _) as l1),
          ((uid2, _) as l2) ) ->
      let set_branches l r set =
        set self_uid a;
        set uid1 { a with executable = l };
        set uid2 { a with executable = r }
      in
      let set_cond_executable b =
        if b then set_branches true false else set_branches false true
      in
      let set_both_executable = set_branches true true in
      if not !converged then
        let flow =
          match (lookup_operand a lhs, lookup_operand a rhs) with
          | OverDefined, _ | _, OverDefined -> set_both_executable
          | NeverDefined, _ | _, NeverDefined -> fun _ -> ()
          | Defined l, Defined r -> set_cond_executable (apply_cond l r cond)
        in
        Flow.Dataflow flow
      else
        let i, changed = Deadcode.rewrite_branch get_args i in
        let i, changed' = rewrite_uses lookup_operand a i in
        let i = fold_conditional (Cfg.CBranch (i, l1, l2)) in
        if changed || changed' then
          Flow.Rewrite Cfg.(unfocus ((First Entry, Last i), empty))
        else Flow.Dataflow (fun _ -> ())
    | Cfg.CBranch _ -> failwith "handle_last: expected cbranch"
    | Cfg.Return i ->
      if not !converged then Flow.Dataflow (fun set -> set self_uid a)
      else
        let i, changed = rewrite_uses lookup_operand a i in
        if changed then
          Flow.Rewrite Cfg.(unfocus ((First Entry, Last (Return i)), empty))
        else Flow.Dataflow (fun _ -> ())
  in
  let pass = (fact, { Flow.ForwardPass.first_out; middle_out; last_outs }) in
  (* todo: mark function arguments as overdefined *)
  let _, (graph, changed) =
    Flow.ForwardPass.solve_and_rewrite
      ~after_analysis:(fun _ -> converged := true)
      pass graph fact.init_info
  in
  (Cfg.Blocks.filter (fun uid _ -> not (fact.skip_block uid)) graph, changed)
