open Normalize
module IntMap = Map.Make (Int)
module IntHashtbl = Utils.IntHashtbl
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

let block_args_fact () =
  let store = IntHashtbl.create Utils.hashtbl_size in
  {
    Flow.init_info = NameMap.empty;
    add_info = NameMap.union (fun _ a b -> Some (OperandSet.union a b));
    changed =
      (fun ~before ~after -> not (NameMap.equal OperandSet.equal before after));
    skip_block = Fun.const false;
    get = IntHashtbl.find store;
    set = IntHashtbl.replace store;
  }

let block_args graph =
  let fact = block_args_fact () in
  let args_tbl = IntHashtbl.create Utils.hashtbl_size in
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
      | Target.Label ((uid', _), args) ->
        begin try
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

let lattice_union a b =
  match (a, b) with
  | NeverDefined, a | a, NeverDefined -> a
  | Defined _, OverDefined | OverDefined, Defined _ -> OverDefined
  | Defined i, Defined j ->
    if i = j then Defined i
    else failwith "lattice_union: two different defined values"
  | OverDefined, OverDefined -> OverDefined

type t = {
  mapping : lattice NameMap.t;
  executable : bool;
}
[@@deriving show, eq]

let state_fact () =
  let store = IntHashtbl.create Utils.hashtbl_size in
  {
    Flow.init_info = { mapping = NameMap.empty; executable = false };
    add_info =
      (fun a b ->
        {
          mapping =
            NameMap.union
              (fun _ a b -> Some (lattice_union a b))
              a.mapping b.mapping;
          executable = a.executable || b.executable;
        });
    changed = (fun ~before ~after -> not (equal before after));
    skip_block =
      (fun uid ->
        uid <> Cfg.entry_uid && not (IntHashtbl.find store uid).executable);
    get = IntHashtbl.find store;
    set = IntHashtbl.replace store;
  }

let is_executable fact uid =
  uid = Cfg.entry_uid || (fact.Flow.get uid).executable

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
  | Ast.Div -> l / r
  | Ast.And -> Int.logand l r
  | Ast.Or -> Int.logor l r
  | Ast.Eq -> if l = r then 1 else 0
  | Ast.Neq -> if l = r then 0 else 1
  | Ast.Lt -> if l < r then 1 else 0
  | Ast.Le -> if l <= r then 1 else 0
  | Ast.Gt -> if l > r then 1 else 0
  | Ast.Ge -> if l >= r then 1 else 0

let apply_cond l r = function
  | Graph.Cond.LT -> l < r
  | LE -> l <= r
  | GT -> l > r
  | GE -> l >= r
  | EQ -> l = r
  | NE -> l <> r

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

let constprop (block_args : OperandSet.t NameMap.t)
    (function_args : Name.t list) graph =
  let fact = state_fact () in
  let converged = ref false in
  let args_tbl = IntHashtbl.create Utils.hashtbl_size in
  let lookup_operand a = function
    | Target.Const c -> Defined c
    | Target.Reg r ->
      (try NameMap.find r a.mapping with Not_found -> NeverDefined)
    | _ -> NeverDefined
  in
  let add_mapping a res = function
    | Some v -> { a with mapping = NameMap.add res v a.mapping }
    | None -> a
  in
  (* mark function arguments as overdefined *)
  let init_info =
    List.fold_left
      (fun acc arg ->
        { acc with mapping = NameMap.add arg OverDefined acc.mapping })
      fact.init_info function_args
  in
  let fact = { fact with init_info } in
  let first_out = function
    | Cfg.Entry -> Flow.Dataflow (fact.get Cfg.entry_uid)
    | Cfg.Label (((uid, _) as l), info) ->
      let a = fact.get uid in
      let update_block_arg a arg =
        let call_args = NameMap.find arg block_args in
        Logs.debug (fun m ->
            m "Call args for phi %a: %s" Name.pp arg
              ([%show: (Cfg.uid * Target.operand) list]
                 (OperandSet.to_list call_args)));
        let get_values acc = function
          | uid, Target.Const i when is_executable fact uid -> Defined i :: acc
          | uid, Target.Reg arg when is_executable fact uid ->
            begin match NameMap.find_opt arg a.mapping with
            | Some NeverDefined -> acc
            | Some v -> v :: acc
            | None -> OverDefined :: acc
            end
          | uid, _ ->
            Logs.debug (fun m -> m "Call block %d not executable" uid);
            acc
        in
        let values =
          call_args |> OperandSet.to_list |> List.fold_left get_values []
        in
        Logs.debug (fun m -> m "Lattices: %s\n" ([%show: lattice list] values));
        let lattice =
          match remove_consecutive_duplicates values with
          | [ v ] -> Some v
          | [] -> None
          | _ -> Some OverDefined
        in
        Logs.debug (fun m ->
            m "Adding mapping %a -> %a\n" Name.pp arg
              (Format.pp_print_option pp_lattice)
              lattice);
        add_mapping a arg lattice
      in
      if not !converged then begin
        let a = List.fold_left update_block_arg a info.args in
        let rewrite_block_arg arg =
          match NameMap.find_opt arg a.mapping with
          | Some (Defined _) -> Name.tombstone
          | _ -> arg
        in
        let args = List.map rewrite_block_arg info.args in
        IntHashtbl.add args_tbl uid args;
        Flow.Dataflow a
      end
      else
        begin match IntHashtbl.find_opt args_tbl uid with
        | Some args when args <> info.args ->
          Flow.Rewrite Cfg.(unfocus @@ label ~args l @@ focus_entry empty)
        | _ -> Flow.Dataflow a
        end
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
    | Target.Alloca (Reg res, _) | Target.Load (Reg res, _) ->
      add_mapping a res (Some OverDefined)
    | Target.Alloca _ ->
      failwith "handle_instruction: alloca destination not a name"
    | Target.Load _ ->
      failwith "handle_instruction: load destination not a name"
    | Target.Store _ -> a
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
    else if
      all_defs_defined () && not (Normalize.Target.is_side_effectful instr)
    then begin
      Logs.debug (fun m ->
          m "Killing dead instruction %a\n" Target.pp_instr instr);
      Flow.Rewrite Cfg.empty
    end
    else
      let instr, changed = rewrite_uses lookup_operand a instr in
      if changed then
        Flow.Rewrite Cfg.(unfocus @@ instruction instr @@ focus_entry empty)
      else Flow.Dataflow a
  in
  let get_args uid =
    List.map (fun n -> Target.Reg n) (IntHashtbl.find args_tbl uid)
  in
  let last_outs uid a = function
    | Cfg.Exit ->
      if not !converged then Flow.Dataflow (fun set -> set Cfg.entry_uid a)
      else Flow.Dataflow (fun _ -> ())
    | Cfg.Branch (i, ((uid, _) as l)) ->
      if not !converged then
        Flow.Dataflow (fun set -> set uid { a with executable = true })
      else
        let i, changed = Deadcode.M.rewrite_branch get_args i in
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
          | OverDefined, _ | _, OverDefined ->
            Logs.debug (fun m -> m "Block %d branches both executable\n" uid);
            set_both_executable
          | NeverDefined, _ | _, NeverDefined ->
            Logs.debug (fun m -> m "Block %d has never defined branches\n" uid);
            fun _ -> ()
          | Defined l, Defined r ->
            Logs.debug (fun m ->
                m "Block %d branches both defined as %d, %d with cond %a\n" uid
                  l r Target.pp_cond cond);
            set_cond_executable (apply_cond l r cond)
        in
        Flow.Dataflow flow
      else
        let i, changed = Deadcode.M.rewrite_branch get_args i in
        let i, changed' = rewrite_uses lookup_operand a i in
        let i = fold_conditional (Cfg.CBranch (i, l1, l2)) in
        if changed || changed' then
          Flow.Rewrite Cfg.(unfocus ((First Entry, Last i), empty))
        else Flow.Dataflow (fun _ -> ())
    | Cfg.CBranch _ -> failwith "handle_last: expected cbranch"
    | Cfg.Return i ->
      if not !converged then Flow.Dataflow (fun set -> set Cfg.entry_uid a)
      else
        let i, changed = rewrite_uses lookup_operand a i in
        if changed then
          Flow.Rewrite Cfg.(unfocus ((First Entry, Last (Return i)), empty))
        else Flow.Dataflow (fun _ -> ())
  in
  let pass = (fact, { Flow.ForwardPass.first_out; middle_out; last_outs }) in
  let _, (graph, changed) =
    Flow.ForwardPass.solve_and_rewrite_thunk
      ~after_analysis:(fun _ -> converged := true)
      pass graph
      (fun () -> fact.get Cfg.entry_uid)
  in
  Logs.debug (fun m ->
      m "Executable blocks: %s\n"
        ([%show: (Cfg.label option * bool) list]
           (List.map
              (fun block ->
                let label = Cfg.block_label block in
                (label, is_executable fact (Cfg.idd label)))
              (Cfg.reverse_postorder_dfs graph))));
  (Cfg.Blocks.filter (fun uid _ -> not (fact.skip_block uid)) graph, changed)

let remove_empty_blocks graph =
  let find_empty _ block acc =
    match block with
    | ( Cfg.Label ((uid, _), { args = []; _ }),
        Cfg.Last (Cfg.Branch (Target.Goto (l, ops), _)) ) ->
      IntMap.add uid (l, ops) acc
    | _ -> acc
  in
  let empty_blocks = Cfg.Blocks.fold find_empty graph IntMap.empty in
  let rewrite_block _ block acc =
    if IntMap.mem (Cfg.id block) empty_blocks then acc
    else
      let h, l = Cfg.(goto_end (unzip block)) in
      let l =
        match l with
        | Cfg.Exit -> Cfg.Exit
        | Cfg.Return i -> Cfg.Return i
        | Cfg.Branch (_, (uid, _)) ->
          begin match IntMap.find_opt uid empty_blocks with
          | Some (lab, ops) -> Cfg.Branch (Target.Goto (lab, ops), lab)
          | None -> l
          end
        | Cfg.CBranch
            (Target.Cbranch (op1, op2, cond, l1, l1args, l2, l2args), _, _) ->
          let l1, l1args =
            match IntMap.find_opt (fst l1) empty_blocks with
            | Some (l1, l1args) -> (l1, l1args)
            | None -> (l1, l1args)
          in
          let l2, l2args =
            match IntMap.find_opt (fst l2) empty_blocks with
            | Some (l2, l2args) -> (l2, l2args)
            | None -> (l2, l2args)
          in
          Cfg.CBranch
            (Target.Cbranch (op1, op2, cond, l1, l1args, l2, l2args), l1, l2)
        | Cfg.CBranch _ -> failwith "InValid conditional branch"
      in
      Cfg.(Blocks.insert (zip (h, Last l)) acc)
  in
  Cfg.Blocks.fold rewrite_block graph Cfg.empty
