let hashtbl_size = 100
let m = 10_000

module IntHashtbl = Hashtbl.Make (Int)
module IntSet = Set.Make (Int)
module IntMap = Graph_intf.IntMap

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
    changed =
      (fun ~before ~after ->
        not (IntMap.equal Int.equal before.distances after.distances));
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
  module RegSet = X86.Target.RegSet
  module State = struct
    type t = {
      mapping : RegSet.t;
      max_register_pressure : int;
      used : RegSet.t;
    }
  end
  type t = {
    live_in : X86.Cfg.uid -> RegSet.t;
    live_out : X86.Cfg.uid -> RegSet.t;
    used_in_block : X86.Cfg.uid -> RegSet.t;
    max_register_pressure : X86.Cfg.uid -> int;
  }
  let fact () =
    let store = IntHashtbl.create hashtbl_size in
    {
      X86.Flow.init_info =
        {
          State.mapping = RegSet.empty;
          used = RegSet.empty;
          max_register_pressure = 0;
        };
      add_info =
        (fun a b ->
          {
            a with
            mapping = RegSet.union a.mapping b.mapping;
            used = RegSet.union a.used b.used;
          });
      changed =
        (fun ~before ~after ->
          RegSet.(
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
        | X86.Target.Reg r -> Some r
        | _ -> None)
      |> RegSet.of_list
    in
    let uses instr = convert_operands instr.X86.Target.uses in
    let defs instr = convert_operands instr.X86.Target.defs in
    let update_mapping mapping a =
      {
        a with
        mapping;
        State.max_register_pressure =
          max a.State.max_register_pressure (RegSet.cardinal mapping);
      }
    in
    let handle_instruction instr a =
      let instr_uses = uses instr in
      let instr_defs = defs instr in
      update_mapping
        RegSet.(union instr_uses (diff a.State.mapping instr_defs))
        { a with used = RegSet.union instr_uses a.used }
    in
    let calc_live_out = function
      | X86.Cfg.Exit -> fact.init_info
      | X86.Cfg.Branch (_, (uid, _)) ->
        update_mapping (fact.get uid).mapping fact.init_info
      | X86.Cfg.CBranch (instr, (uid1, _), (uid2, _)) ->
        handle_instruction instr
        @@ update_mapping
             (RegSet.union (fact.get uid1).mapping (fact.get uid2).mapping)
        @@ fact.init_info
      | X86.Cfg.Return instr -> handle_instruction instr fact.init_info
    in
    let analysis =
      {
        (* todo: handle block arguments *)
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

module Make
    (Loop :
      Loopnesting.S
        with type Dom.label = X86.Cfg.label
         and type Dom.position = int
         and type Dom.uid = X86.Cfg.uid)
    (M : sig
      val k : int
      val next_use_distances : X86.Cfg.uid -> int IntMap.t
      val liveness : Liveness.t
    end) =
struct
  let compare dists a b =
    match
      X86.Target.
        (IntMap.find_opt (index a) dists, IntMap.find_opt (index b) dists)
    with
    | None, None -> 0
    | None, _ -> 1
    | _, None -> -1
    | Some dist1, Some dist2 -> dist1 - dist2

  let uid p = X86.Cfg.idd @@ Loop.Dom.label_of_position p
  module RegSet = X86.Target.RegSet

  let init_usual (wexit : Loop.Dom.position -> RegSet.t)
      (block : Loop.Dom.position) =
    let freq = IntHashtbl.create hashtbl_size in
    let take = ref RegSet.empty in
    let cand = ref RegSet.empty in
    let preds_length = List.length (Loop.Dom.predecessors block) in
    List.iter
      (fun pred ->
        RegSet.iter
          (fun var ->
            let var_idx = X86.Target.index var in
            IntHashtbl.replace freq var_idx
              ((try IntHashtbl.find freq var_idx with Not_found -> 0) + 1);
            cand := RegSet.add var !cand;
            if IntHashtbl.find freq var_idx = preds_length then begin
              cand := RegSet.remove var !cand;
              take := RegSet.add var !take
            end)
          (wexit pred))
      (Loop.Dom.predecessors block);
    let dists = M.next_use_distances (uid block) in
    let cand = List.sort (compare dists) (RegSet.to_list !cand) in
    RegSet.(union !take (of_list (List.take (M.k - cardinal !take) cand)))

  let rec get_loop_nodes (node : Loop.Dom.position) : Loop.PositionSet.t =
    let nodes = Iarray.get Loop.loop_nodes node in
    let add_loop_node node acc =
      if Loop.PositionSet.mem node Loop.loop_headers then
        Loop.PositionSet.(union (get_loop_nodes node) (add node acc))
      else Loop.PositionSet.add node acc
    in
    Loop.PositionSet.fold add_loop_node nodes (Loop.PositionSet.singleton node)

  let init_loop_header (block : Loop.Dom.position) =
    let loop = get_loop_nodes block in
    Format.printf "Loop nodes: %s\n"
      ([%show: X86.Cfg.label option list]
         (Loop.PositionSet.to_list loop |> List.map Loop.Dom.label_of_position));
    let alive = M.liveness.live_in (uid block) in
    let used_in_loop =
      Loop.PositionSet.fold
        (fun node -> RegSet.union (M.liveness.used_in_block (uid node)))
        loop RegSet.empty
    in
    Format.printf "Used in loop: %s\n"
      ([%show: X86.Cfg.regs] (RegSet.to_list used_in_loop));
    let cand = RegSet.inter alive used_in_loop in
    let dists = M.next_use_distances (uid block) in
    let max_pressure =
      Loop.PositionSet.fold
        (fun node -> max (M.liveness.max_register_pressure (uid node)))
        loop 0
    in
    if RegSet.cardinal cand < M.k then (
      let live_through = RegSet.diff alive cand in
      Format.printf "Live through: %s\n"
        ([%show: X86.Cfg.regs] (RegSet.to_list live_through));
      let free_loop = M.k - max_pressure + RegSet.cardinal live_through in
      let live_through =
        List.sort (compare dists) (RegSet.to_list live_through)
      in
      RegSet.(union cand (of_list (List.take free_loop live_through))))
    else
      let cand = List.sort (compare dists) (RegSet.to_list cand) in
      RegSet.of_list (List.take M.k cand)

  type min_state = {
    w : RegSet.t;
    s : RegSet.t;
  }

  type spill_state = {
    select_state : Select_x86.State.t;
    spill_mapping : X86.Target.operand IntHashtbl.t;
    copies : X86.Target.reg IntHashtbl.t;
  }

  let init (state : Select_x86.State.t) =
    {
      select_state = state;
      spill_mapping = IntHashtbl.create hashtbl_size;
      copies = IntHashtbl.create hashtbl_size;
    }

  open struct
    let get_slot (state : spill_state) v =
      let id = X86.Target.index v in
      try IntHashtbl.find state.spill_mapping id
      with Not_found ->
        let slot = state.select_state.new_stack_slot 8 in
        IntHashtbl.add state.spill_mapping id slot;
        slot
  end

  let spill (state : spill_state) v =
    X86.Target.mov ~dest:(get_slot state v) ~src:(X86.Target.Reg v)

  let reload (state : spill_state) v =
    let slot = get_slot state v in
    let v' = state.select_state.fresh_vreg Int in
    IntHashtbl.add state.copies (X86.Target.index v) v';
    X86.Target.mov ~dest:(X86.Target.Reg v') ~src:slot

  let limit (state : spill_state) (next_use_distances : int IntMap.t)
      ({ w; s } : min_state) (head : X86.Cfg.head) (m : int) :
      X86.Cfg.head * min_state =
    let w = List.sort (compare next_use_distances) (RegSet.to_list w) in
    let head, s =
      List.fold_left
        (fun (head, s) v ->
          let head =
            if
              (not (RegSet.mem v s))
              && IntMap.mem (X86.Target.index v) next_use_distances
            then X86.Cfg.Head (head, Instruction (spill state v))
            else head
          in
          (head, RegSet.remove v s))
        (head, s) (List.drop m w)
    in
    let w = RegSet.of_list (List.take m w) in
    (head, { w; s })

  let min_algorithm (state : spill_state) (zblock : X86.Cfg.zblock)
      ({ w; s } : min_state) : X86.Cfg.zblock * min_state =
    let next_use_distances = M.next_use_distances X86.Cfg.(id (zip zblock)) in
    let rec go w s = function
      | head, X86.Cfg.Tail (Instruction instr, tail) ->
        let r = RegSet.diff (X86.Target.uses instr) w in
        (* todo: just use RegSet.union r ? *)
        let w, s =
          RegSet.fold
            (fun use (w, s) -> (RegSet.add use w, RegSet.add use s))
            r (w, s)
        in
        let head, { w; s } = limit state next_use_distances { w; s } head M.k in
        let head = X86.Cfg.Head (head, Instruction instr) in
        (* add reloads for vars in r *)
        let head =
          RegSet.fold
            (fun var head ->
              X86.Cfg.Head (head, Instruction (reload state var)))
            r head
        in
        let head, { w; s } =
          limit state next_use_distances { w; s } head
            (M.k - RegSet.cardinal (X86.Target.defs instr))
        in
        let w = RegSet.union w (X86.Target.defs instr) in
        go w s (head, tail)
      | head, X86.Cfg.Last l ->
        let handle_instruction instr =
          let r = RegSet.diff (X86.Target.uses instr) w in
          let w, s =
            RegSet.fold
              (fun use (w, s) -> (RegSet.add use w, RegSet.add use s))
              r (w, s)
          in
          limit state next_use_distances { w; s } head M.k
        in
        let head, min_state =
          match l with
          | X86.Cfg.Exit -> (head, { w; s })
          | X86.Cfg.Branch (i, _) -> handle_instruction i
          | X86.Cfg.CBranch (i, _, _) -> handle_instruction i
          | X86.Cfg.Return i -> handle_instruction i
        in
        ((head, X86.Cfg.Last l), min_state)
    in
    go w s zblock

  let spill (state : spill_state) (graph : X86.Cfg.graph) : X86.Cfg.graph =
    let processed = Array.make Loop.Dom.size false in
    let saved_w_entry = Array.make Loop.Dom.size RegSet.empty in
    let saved_s_entry = Array.make Loop.Dom.size RegSet.empty in
    let saved_w_exit = Array.make Loop.Dom.size RegSet.empty in
    let saved_s_exit = Array.make Loop.Dom.size RegSet.empty in
    let insert_coupling curr graph pred =
      let reloads = RegSet.diff saved_w_entry.(curr) saved_w_exit.(pred) in
      let spills =
        RegSet.(
          inter
            (diff saved_s_entry.(curr) saved_s_exit.(pred))
            saved_w_exit.(pred))
      in
      state.select_state.curr_block := uid pred;
      let zblock, graph = X86.Cfg.focus (uid pred) graph in
      let head, last = X86.Cfg.goto_end zblock in
      let insert_instr f var head = X86.Cfg.Head (head, Instruction (f var)) in
      let head = RegSet.fold (insert_instr (reload state)) reloads head in
      let head = RegSet.fold (insert_instr (spill state)) spills head in
      X86.Cfg.unfocus ((head, Last last), graph)
    in
    let spill_block (state : spill_state) (graph : X86.Cfg.graph)
        (block_uid : X86.Cfg.uid) : X86.Cfg.graph =
      let pos = Loop.Dom.position_of_uid block_uid in
      let w_entry =
        if Loop.PositionSet.mem pos Loop.loop_headers then init_loop_header pos
        else init_usual (fun pos -> saved_w_exit.(pos)) pos
      in
      (* intersection(union(s_exit for all predecessors), w_entry) *)
      let s_entry =
        RegSet.inter
          (List.fold_left
             (fun acc pred -> RegSet.union acc saved_s_exit.(pred))
             RegSet.empty
             (Loop.Dom.predecessors pos))
          w_entry
      in
      saved_w_entry.(pos) <- w_entry;
      saved_s_entry.(pos) <- s_entry;
      (* go back to predecessors and insert coupling code *)
      let graph =
        Loop.Dom.predecessors pos
        |> List.filter (fun pred -> processed.(pred))
        |> List.fold_left (insert_coupling pos) graph
      in
      state.select_state.curr_block := block_uid;
      let zblock, graph = X86.Cfg.focus block_uid graph in
      let zblock, { w = w_exit; s = s_exit } =
        min_algorithm state zblock { w = w_entry; s = s_entry }
      in
      (* save w_exit and s_exit for block id *)
      processed.(pos) <- true;
      saved_w_exit.(pos) <- w_exit;
      saved_s_exit.(pos) <- s_exit;
      let graph = X86.Cfg.unfocus (zblock, graph) in
      Loop.Dom.successors pos
      |> List.filter (fun succ -> processed.(succ))
      |> List.fold_left (fun graph succ -> insert_coupling succ graph pos) graph
    in
    (* todo: can this be replaced with iterating from 0 to Loop.Dom.size-1? *)
    let rpo = X86.Cfg.reverse_postorder_dfs graph in
    List.fold_left
      (fun graph block ->
        spill_block state graph X86.Cfg.(idd (block_label block)))
      graph rpo
end
