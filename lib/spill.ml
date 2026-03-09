let hashtbl_size = 100
let m = 10_000

module IntHashtbl = Hashtbl.Make (Int)
module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)

let count_instructions (tail : X86.Cfg.tail) =
  let rec go acc = function
    | X86.Printer.Last _ -> acc
    | X86.Printer.Tail (_, t) -> go (acc + 1) t
  in
  go 1 tail

type state = {
  distances : int IntMap.t;
  (* temporary for each block *)
  first_use : int IntMap.t;
  count : int;
}
let fact () =
  let store = IntHashtbl.create hashtbl_size in
  (* if variable doesn't exist in distances map it has distance of infinity *)
  let init_info =
    { distances = IntMap.empty; first_use = IntMap.empty; count = 0 }
  in
  {
    X86.Flow.init_info;
    add_info =
      (fun a b ->
        {
          init_info with
          distances =
            IntMap.union
              (fun _ v1 v2 -> Some (min v1 v2))
              a.distances b.distances;
        });
    changed = (fun ~before ~after -> before.distances <> after.distances);
    skip_block = Fun.const false;
    get = IntHashtbl.find store;
    set = IntHashtbl.replace store;
  }

let next_use_distances
    (module Loop : Loopnesting.S
      with type Dom.label = X86.Cfg.label
       and type Dom.position = int
       and type Dom.uid = X86.Cfg.uid) (graph : X86.Cfg.graph) :
    X86.Cfg.uid -> int IntMap.t =
  (* edges leading out of loops:
     if u in loop_headers then header(v) != u else header(v) != header(u) *)
  (* each block has a unique length because critical edges are assumed
     to already be split and the only different case is edges leading out
     of loops, which must originate from nodes with multiple successors.
     That means that destination nodes must have only one predecessor if
     they are edges out of loops, otherwise its length is 0. *)
  let block_lengths =
    Array.init Loop.Dom.size @@ fun v ->
    let preds = Loop.Dom.predecessors v in
    match preds with
    | [ u ]
      when if Loop.(PositionSet.mem u loop_headers) then Loop.loop_header v <> u
           else Loop.(loop_header v <> loop_header u) ->
      m
    | _ -> 0
  in
  (* track current instruction number offset starting from 0
     then distance is num_instructions[block] - offset *)
  let block_num_instructions =
    Array.init Loop.Dom.size @@ fun p ->
    let uid = X86.Cfg.idd (Loop.Dom.label_of_position p) in
    let (_, tail), _ = X86.Cfg.focus uid graph in
    count_instructions tail
  in
  let fact = fact () in
  let handle_instruction i a =
    let handle_use acc = function
      | X86.Target.Reg r -> IntMap.add (X86.Target.index r) a.count acc
      | _ -> acc
    in
    let first_use = List.fold_left handle_use a.first_use i.X86.Target.uses in
    { a with first_use; count = a.count + 1 }
  in
  let first_in a first =
    let pos =
      match first with
      | X86.Cfg.Entry -> Loop.Dom.position_of_uid X86.Cfg.entry_uid
      | X86.Cfg.Label ((uid, _), _) -> Loop.Dom.position_of_uid uid
    in
    let l = block_lengths.(pos) in
    let num_instructions = block_num_instructions.(pos) in
    let distances =
      a.distances
      |> IntMap.map (fun dist -> dist + num_instructions)
      |> IntMap.fold
           (fun v offset -> IntMap.add v (num_instructions - offset))
           a.first_use
      |> IntMap.map (fun dist -> dist + l)
    in
    { fact.init_info with distances }
  in
  let middle_in a (X86.Cfg.Instruction i) = handle_instruction i a in
  let last_in _ = function
    | X86.Cfg.Exit -> { fact.init_info with count = 1 }
    | X86.Cfg.Branch (i, (uid', _)) -> handle_instruction i @@ fact.get uid'
    | X86.Cfg.CBranch (i, (uid1, _), (uid2, _)) ->
      handle_instruction i @@ fact.add_info (fact.get uid1) (fact.get uid2)
    | X86.Cfg.Return i -> handle_instruction i fact.init_info
  in
  let analysis =
    (fact, { X86.Flow.BackwardAnalysis.first_in; middle_in; last_in })
  in
  let _ = X86.Flow.BackwardAnalysis.run analysis graph in
  fun uid -> (fact.get uid).distances

module Liveness = struct
  module State = struct
    type t = {
      mapping : IntSet.t;
      max_register_pressure : int;
      used : IntSet.t;
    }
  end
  type t = {
    live_in : X86.Cfg.uid -> IntSet.t;
    live_out : X86.Cfg.uid -> IntSet.t;
    used_in_block : X86.Cfg.uid -> IntSet.t;
    max_register_pressure : X86.Cfg.uid -> int;
  }
  let fact () =
    let store = IntHashtbl.create hashtbl_size in
    {
      X86.Flow.init_info =
        {
          State.mapping = IntSet.empty;
          used = IntSet.empty;
          max_register_pressure = 0;
        };
      add_info =
        (fun a b ->
          {
            a with
            mapping = IntSet.union a.mapping b.mapping;
            used = IntSet.union a.used b.used;
          });
      changed =
        (fun ~before ~after ->
          IntSet.(
            cardinal after.mapping > cardinal before.mapping
            || cardinal after.used > cardinal before.used));
      skip_block = Fun.const false;
      get = IntHashtbl.find store;
      set = IntHashtbl.replace store;
    }
  let calc graph : t =
    let fact = fact () in
    let convert_operands ops =
      ops
      |> List.filter_map (function
        | X86.Target.Reg r -> Some (X86.Target.index r)
        | _ -> None)
      |> IntSet.of_list
    in
    let uses instr = convert_operands instr.X86.Target.uses in
    let defs instr = convert_operands instr.X86.Target.defs in
    let update_mapping mapping a =
      {
        a with
        mapping;
        State.max_register_pressure =
          max a.State.max_register_pressure (IntSet.cardinal mapping);
      }
    in
    let handle_instruction instr a =
      update_mapping
        (IntSet.union (uses instr) (IntSet.diff a.State.mapping (defs instr)))
        { a with used = IntSet.union (uses instr) a.used }
    in
    let calc_live_out = function
      | X86.Cfg.Exit -> fact.init_info
      | X86.Cfg.Branch (_, (uid, _)) ->
        update_mapping (fact.get uid).mapping fact.init_info
      | X86.Cfg.CBranch (instr, (uid1, _), (uid2, _)) ->
        handle_instruction instr
        @@ update_mapping
             (IntSet.union (fact.get uid1).mapping (fact.get uid2).mapping)
        @@ fact.init_info
      | X86.Cfg.Return instr -> handle_instruction instr fact.init_info
    in
    let analysis =
      {
        X86.Flow.BackwardAnalysis.first_in = (fun a _ -> a);
        middle_in = (fun a (Instruction instr) -> handle_instruction instr a);
        last_in = Fun.const calc_live_out;
      }
    in
    let analysis = (fact, analysis) in
    let _ = X86.Flow.BackwardAnalysis.run analysis graph in
    {
      live_in = (fun uid -> (fact.get uid).mapping);
      live_out =
        (fun uid ->
          (calc_live_out X86.Cfg.(last @@ fst @@ focus uid graph)).mapping);
      used_in_block = (fun uid -> (fact.get uid).used);
      max_register_pressure = (fun uid -> (fact.get uid).max_register_pressure);
    }
end

module InitWEntry
    (Extra :
      Graph.Extra with type label = X86.Cfg.label and type graph = X86.Cfg.graph)
    (M : sig
      val k : int
      val next_use_distances : X86.Cfg.uid -> int IntMap.t
    end) =
struct
  let compare dists a b =
    match (IntMap.find_opt a dists, IntMap.find_opt b dists) with
    | None, None -> 0
    | None, _ -> 1
    | _, None -> -1
    | Some dist1, Some dist2 -> dist1 - dist2

  let init_usual (wexit : X86.Cfg.uid -> IntSet.t) (block : Extra.position) =
    let freq = IntHashtbl.create hashtbl_size in
    let take = ref IntSet.empty in
    let cand = ref IntSet.empty in
    let preds_length = List.length (Extra.predecessors block) in
    List.iter
      (fun pred ->
        let pred = X86.Cfg.idd @@ Extra.label_of_position pred in
        IntSet.iter
          (fun var ->
            IntHashtbl.replace freq var (IntHashtbl.find freq var + 1);
            cand := IntSet.add var !cand;
            if IntHashtbl.find freq var = preds_length then begin
              cand := IntSet.remove var !cand;
              take := IntSet.add var !take
            end)
          (wexit pred))
      (Extra.predecessors block);
    let dists =
      M.next_use_distances @@ X86.Cfg.idd @@ Extra.label_of_position block
    in
    let cand = List.sort (compare dists) (IntSet.to_list !cand) in
    IntSet.union !take
      (IntSet.of_list (List.take (M.k - IntSet.cardinal !take) cand))
end
