module Cfg = Normalize.Cfg
module IntHashtbl = Hashtbl.Make (Int)
module Flow = Normalize.Flow
module Name = Normalize.Name
module NameMap = struct
  include CCMap.Make (struct
    include Name
    let compare = compare
  end)
  let pp pp_v = pp Name.pp pp_v
end
module NameSet = Normalize.NameSet

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

let hashtbl_size = 100
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

let block_args_fact () =
  let store = IntHashtbl.create hashtbl_size in
  {
    Flow.init_info = NameMap.empty;
    add_info = NameMap.union (fun _ a b -> Some (NameSet.union a b));
    changed =
      (fun ~before ~after -> not (NameMap.equal NameSet.equal before after));
    skip_block = Fun.const false;
    get = IntHashtbl.find store;
    set = IntHashtbl.add store;
  }

let block_args graph =
  let fact = block_args_fact () in
  let handle_first a = function
    | Cfg.Entry -> a
    | Cfg.Label (_, info) ->
      List.fold_left (fun a arg -> NameMap.add arg NameSet.empty a) a info.args
  in
  let analysis =
    {
      Flow.BackwardAnalysis.first_in = handle_first;
      (* todo: calls add to args set *)
      middle_in = (fun a _ -> a);
      (* todo: merge maps of successors *)
      last_in = (fun _ -> NameMap.empty);
    }
  in
  let analysis = (fact, analysis) in
  let _ = Flow.BackwardAnalysis.run analysis graph in
  fact.get Cfg.entry_uid

let constprop graph =
  let fact = state_fact () in
  let handle_instruction _instr _a = failwith "" in
  let handle_middle a instr = Flow.Dataflow (handle_instruction instr a) in
  let handle_last a = function
    | Cfg.Exit -> Flow.Dataflow (fun _ -> ())
    | Cfg.Branch (_, (uid, _)) -> Flow.Dataflow (fun set -> set uid a)
    | Cfg.CBranch (_, (uid1, _), (uid2, _)) ->
      Flow.Dataflow
        (* todo: for each block arg, if all calls resolve to the same constant,
        set arg to the constant in the mapping *)
        (* unused args can be "removed" by replacing them with a tombstone *)
        (fun set ->
          set uid1 a;
          set uid2 a)
    | Cfg.Return (_, _) -> Flow.Dataflow (fun _ -> ())
  in
  let pass =
    {
      Flow.ForwardPass.middle_out =
        (fun a (Instruction instr) -> handle_middle a instr);
      last_outs = handle_last;
    }
  in
  let pass = (fact, pass) in
  snd @@ Flow.ForwardPass.solve_and_rewrite pass graph fact.init_info
