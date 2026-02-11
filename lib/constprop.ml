module Cfg = Normalize.Cfg
module IntHashtbl = Hashtbl.Make (Int)
module Flow = Normalize.Flow
module Target = Normalize.Target
module Name = Normalize.Name
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
  let pp =
    let pp_tuple fmt (uid, op) =
      Format.fprintf fmt "(%d,%a)" uid Target.pp_operand op
    in
    pp pp_tuple
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
  let handle_first a = function
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
  let handle_last uid =
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
    | Cfg.Return (_, _) -> NameMap.empty
  in
  let analysis =
    {
      Flow.BackwardAnalysis.first_in = handle_first;
      middle_in = (fun a _ -> a);
      last_in = handle_last;
    }
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
  executable : bool;
}
[@@deriving show, eq]

let state_fact () =
  let store = IntHashtbl.create hashtbl_size in
  {
    Flow.init_info = { mapping = NameMap.empty; executable = false };
    add_info =
      (fun a b ->
        {
          mapping = NameMap.union (fun _ _ a -> Some a) a.mapping b.mapping;
          executable = b.executable;
        });
    changed = (fun ~before ~after -> not (equal before after));
    skip_block = (fun uid -> not (IntHashtbl.find store uid).executable);
    get = IntHashtbl.find store;
    set = IntHashtbl.add store;
  }

let rec remove_consecutive_duplicates = function
  | [] -> []
  | [ a ] -> [ a ]
  | a :: b :: rest ->
    if a = b then remove_consecutive_duplicates (b :: rest)
    else a :: remove_consecutive_duplicates (b :: rest)

let constprop (block_args : OperandSet.t NameMap.t) graph =
  let fact = state_fact () in
  let saved_args = IntHashtbl.create hashtbl_size in
  let lookup_operand op a =
    match op with
    | Target.Const c -> Defined c
    | Target.Reg r -> begin
      try NameMap.find r a.mapping with Not_found -> NeverDefined
    end
    | _ -> NeverDefined
  in
  let handle_first = function
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
        match remove_consecutive_duplicates values with
        | [ v ] -> { a with mapping = NameMap.add arg v a.mapping }
        | [] -> a
        | _ -> { a with mapping = NameMap.add arg OverDefined a.mapping }
      in
      let a' = List.fold_left update_block_arg a info.args in
      if a' <> a then Flow.Dataflow a'
      else begin
        let rewrite_block_arg arg =
          match NameMap.find_opt arg a.mapping with
          | Some (Defined _) -> Name.tombstone
          | _ -> arg
        in
        let args = List.map rewrite_block_arg info.args in
        IntHashtbl.add saved_args uid (List.map (fun n -> Target.Reg n) args);
        Flow.Rewrite Cfg.(unfocus @@ label ~args l @@ focus_entry empty)
      end
  in
  let handle_instruction a = function
    | Target.Bop (Reg res, bop, lhs, rhs) ->
      let res_value =
        match (bop, lookup_operand lhs a, lookup_operand rhs a) with
        | _, OverDefined, _ | _, _, OverDefined -> Some OverDefined
        | _, NeverDefined, _ | _, _, NeverDefined -> None
        | Ast.Add, Defined a, Defined b -> Some (Defined (a + b))
        | _ -> None (* todo: remove *)
      in
      begin match res_value with
      | Some v -> { a with mapping = NameMap.add res v a.mapping }
      | None -> a
      end
    | Target.Call (Reg r, _, _) ->
      { a with mapping = NameMap.add r OverDefined a.mapping }
    | _ -> a
  in
  let handle_middle a instr = Flow.Dataflow (handle_instruction a instr) in
  let handle_last a = function
    | Cfg.Exit -> Flow.Dataflow (fun _ -> ())
    | Cfg.Branch (_, (uid, _)) ->
      Flow.Dataflow (fun set -> set uid { a with executable = true })
    | Cfg.CBranch (_, (uid1, _), (uid2, _)) ->
      Flow.Dataflow
        (fun set ->
          set uid1 a;
          set uid2 a)
    | Cfg.Return (_, _) -> Flow.Dataflow (fun _ -> ())
  in
  let pass =
    {
      Flow.ForwardPass.first_out = handle_first;
      middle_out = (fun a (Instruction instr) -> handle_middle a instr);
      last_outs = handle_last;
    }
  in
  let pass = (fact, pass) in
  (* todo: mark function arguments as overdefined *)
  snd @@ Flow.ForwardPass.solve_and_rewrite pass graph fact.init_info
