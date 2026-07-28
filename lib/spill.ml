module IntHashtbl = Utils.IntHashtbl
module IntMap = Utils.IntMap

module NextUseDistances = struct
  module type S = sig
    module G : Graph.S
    type distances = {
      at_block : G.uid -> int IntMap.t;
      at_instruction : G.uid -> int -> int IntMap.t;
    }
    val calc : G.graph -> distances
  end

  let m = 10_000

  module Make
      (Target : Isa.Target)
      (G :
        Graph.S
          with type Target.reg = Target.reg
           and type Target.operand = Target.operand
           and type Target.instr = Target.instr)
      (Flow : Dataflow.S with module G = G)
      (Loop :
        Loopnesting.S
          with type Dom.label = G.label
           and type Dom.position = int
           and type Dom.uid = G.uid) : S with module G = G = struct
    module G = G
    let count_instructions (tail : G.tail) =
      let rec go acc = function
        | G.Tail (_, t) -> go (acc + 1) t
        | Last _ -> acc
      in
      go 1 tail

    type state = {
      distances : int IntMap.t;
      distances_per_instruction : int IntMap.t array;
      block_pos : int;
      count : int;
    }
    let fact () =
      let store = IntHashtbl.create Utils.hashtbl_size in
      (* if variable doesn't exist in distances map it has distance of infinity *)
      let init_info =
        {
          distances = IntMap.empty;
          distances_per_instruction = Array.make 0 IntMap.empty;
          block_pos = 0;
          count = 0;
        }
      in
      {
        Flow.init_info;
        add_info =
          (fun a b ->
            {
              a with
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

    type distances = {
      at_block : G.uid -> int IntMap.t;
      at_instruction : G.uid -> int -> int IntMap.t;
    }

    (* next use distances need to be calculated per instruction *)
    let calc (graph : G.graph) : distances =
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
          when if Loop.(PositionSet.mem u loop_headers) then
                 Loop.loop_header v <> u
               else Loop.(loop_header v <> loop_header u) ->
          m
        | _ -> 0
      in
      (* track current instruction number offset starting from 0
         then distance is num_instructions[block] - offset *)
      let block_num_instructions =
        Array.init Loop.Dom.size @@ fun p ->
        let uid = G.idd (Loop.Dom.label_of_position p) in
        let (_, tail), _ = G.focus uid graph in
        count_instructions tail
      in
      let fact = fact () in
      let handle_instruction i a =
        let l = block_lengths.(a.block_pos) in
        let num_instructions = block_num_instructions.(a.block_pos) in
        let handle_use acc r =
          (IntMap.add (Target.index r) (l + num_instructions - a.count) acc, r)
        in
        let distances, _ = Target.fold_reg_uses handle_use a.distances i in
        a.distances_per_instruction.(num_instructions - 1 - a.count) <-
          distances;
        { a with distances; count = a.count + 1 }
      in
      let first_in a _ = { a with count = 0 } in
      let middle_in a (G.Instruction i) = handle_instruction i a in
      let transfer block_pos fact =
        let l = block_lengths.(block_pos) in
        let num_instructions = block_num_instructions.(block_pos) in
        let distances =
          IntMap.map (fun dist -> l + num_instructions + dist) fact.distances
        in
        let distances_per_instruction =
          Array.make num_instructions IntMap.empty
        in
        distances_per_instruction.(num_instructions - 1) <- distances;
        { fact with block_pos; distances_per_instruction; distances }
      in
      let last_in uid =
        let pos = Loop.Dom.position_of_uid uid in
        let lookup uid' =
          let pos' = Loop.Dom.position_of_uid uid' in
          (* if edge is a loop backedge, then any next-use distances will be after the
             redefinition of the variable making them invalid *)
          if Loop.Dom.dominates pos' pos then fact.init_info else fact.get uid'
        in
        function
        | G.Exit -> { (transfer pos fact.init_info) with count = 1 }
        | Branch (i, (uid', _)) ->
          handle_instruction i @@ transfer pos @@ lookup uid'
        | CBranch (i, (uid1, _), (uid2, _)) ->
          handle_instruction i @@ transfer pos
          @@ fact.add_info (lookup uid1) (lookup uid2)
        | Return i -> handle_instruction i @@ transfer pos fact.init_info
      in
      let analysis =
        (fact, { Flow.BackwardAnalysis.first_in; middle_in; last_in })
      in
      let _ = Flow.BackwardAnalysis.run analysis graph in
      {
        at_block = (fun uid -> (fact.get uid).distances);
        at_instruction =
          (fun uid instr_num ->
            (fact.get uid).distances_per_instruction.(instr_num));
      }
  end
end

module Liveness = struct
  module type S = sig
    module Target : Isa.Target
    module G : Graph.S
    type t = {
      live_in : G.uid -> Target.RegSet.t;
      live_out : G.uid -> Target.RegSet.t;
      used_in_block : G.uid -> Target.RegSet.t;
      dies : G.uid -> G.Target.reg -> int option;
      max_register_pressure : G.uid -> int;
    }
    val calc : G.graph -> t
  end
  module Make
      (Target : Isa.Target)
      (G :
        Graph.S
          with type Target.reg = Target.reg
           and type Target.instr = Target.instr)
      (Flow : Dataflow.S with module G = G) :
    S with module Target = Target and module G = G = struct
    module Target = Target
    module G = G
    module RegSet = Target.RegSet
    module RegMap = Target.RegMap
    module State = struct
      type t = {
        mapping : RegSet.t;
        max_register_pressure : int;
        used : RegSet.t;
        dies : int RegMap.t;
        count : int;
      }
    end
    type t = {
      live_in : G.uid -> RegSet.t;
      live_out : G.uid -> RegSet.t;
      used_in_block : G.uid -> RegSet.t;
      dies : G.uid -> G.Target.reg -> int option;
      max_register_pressure : G.uid -> int;
    }
    let fact () =
      let store = IntHashtbl.create Utils.hashtbl_size in
      {
        Flow.init_info =
          {
            State.mapping = RegSet.empty;
            used = RegSet.empty;
            max_register_pressure = 0;
            dies = RegMap.empty;
            count = 0;
          };
        add_info =
          (fun a b ->
            let mapping = RegSet.union a.mapping b.mapping in
            {
              a with
              mapping;
              used = RegSet.union a.used b.used;
              (* Updated mapping could set more variables as live out so remove those from dies *)
              dies =
                RegSet.fold
                  (fun reg acc -> RegMap.remove reg acc)
                  mapping
                  RegMap.(union (fun _ _ b -> Some b) a.dies b.dies);
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
      let add_reg map reg = (RegSet.add reg map, reg) in
      let uses instr = fst @@ Target.fold_reg_uses add_reg RegSet.empty instr in
      let defs instr = fst @@ Target.fold_reg_defs add_reg RegSet.empty instr in
      let update_mapping mapping a =
        {
          a with
          mapping;
          State.max_register_pressure =
            max a.State.max_register_pressure (RegSet.cardinal mapping);
        }
      in
      let update_dead uses (a : State.t) =
        (* died: uses in instruction that aren't in a's mapping *)
        let dies =
          RegSet.fold
            (fun dead acc ->
              if RegMap.mem dead acc then acc else RegMap.add dead a.count acc)
            (RegSet.diff uses a.mapping)
            a.dies
        in
        { a with dies }
      in
      let finish_dead (a : State.t) =
        { a with dies = RegMap.map (fun off -> a.count - 1 - off) a.dies }
      in
      let first_in (a : State.t) = function
        | G.Entry -> finish_dead a
        | G.Label (_, info) ->
          let uses = RegSet.of_list info.args in
          let a = update_dead uses a in
          finish_dead
          @@ update_mapping RegSet.(diff a.mapping (of_list info.args)) a
      in
      let handle_instruction instr (a : State.t) =
        let instr_uses = uses instr in
        let instr_defs = defs instr in
        let a = update_dead instr_uses a in
        let a = update_dead instr_defs a in
        update_mapping
          RegSet.(union instr_uses (diff a.mapping instr_defs))
          { a with used = RegSet.union instr_uses a.used; count = a.count + 1 }
      in
      let calc_live_out = function
        | G.Exit -> fact.init_info
        | Branch (instr, (uid, _)) ->
          handle_instruction instr
          @@ update_mapping (fact.get uid).mapping fact.init_info
        | CBranch (instr, (uid1, _), (uid2, _)) ->
          handle_instruction instr
          @@ update_mapping
               (RegSet.union (fact.get uid1).mapping (fact.get uid2).mapping)
          @@ fact.init_info
        | Return instr -> handle_instruction instr fact.init_info
      in
      let analysis =
        {
          Flow.BackwardAnalysis.first_in;
          middle_in = (fun a (Instruction instr) -> handle_instruction instr a);
          last_in = Fun.const calc_live_out;
        }
      in
      let analysis = (fact, analysis) in
      let _ = Flow.BackwardAnalysis.run analysis graph in
      {
        live_in = (fun uid -> (fact.get uid).mapping);
        live_out =
          (fun uid ->
            (calc_live_out G.(last @@ fst @@ focus uid graph)).mapping);
        used_in_block = (fun uid -> (fact.get uid).used);
        dies = (fun uid reg -> RegMap.find_opt reg (fact.get uid).dies);
        max_register_pressure =
          (fun uid -> (fact.get uid).max_register_pressure);
      }
  end
end

module Make
    (Target : Isa.Target)
    (G :
      Graph.S
        with type Target.reg = Target.reg
         and type Target.instr = Target.instr)
    (State : Isa.State with module Target = Target)
    (Liveness : Liveness.S with module Target = Target and module G = G)
    (Loop :
      Loopnesting.S
        with type Dom.label = G.label
         and type Dom.position = int
         and type Dom.uid = G.uid)
    (NextUseDistances : NextUseDistances.S with module G = G)
    (M : sig
      val reg_class : Target.reg_class
      val k : int
      val next_use_distances : NextUseDistances.distances
      val liveness : Liveness.t
    end) =
struct
  let compare dists a b =
    match
      ( IntMap.find_opt (Target.index a) dists,
        IntMap.find_opt (Target.index b) dists )
    with
    | None, None -> 0
    | None, _ -> 1
    | _, None -> -1
    | Some dist1, Some dist2 -> dist1 - dist2

  let infinite_distance v next_use_distances =
    not (IntMap.mem (Target.index v) next_use_distances)

  let uid p = G.idd @@ Loop.Dom.label_of_position p
  module RegSet = Target.RegSet
  module RegHashtbl = CCHashtbl.Make (Target.Reg)

  let init_usual (wexit : Loop.Dom.position -> RegSet.t)
      (block : Loop.Dom.position) =
    let freq = IntHashtbl.create Utils.hashtbl_size in
    let take = ref RegSet.empty in
    let cand = ref RegSet.empty in
    let preds_length = List.length (Loop.Dom.predecessors block) in
    List.iter
      (fun pred ->
        RegSet.iter
          (fun var ->
            let var_idx = Target.index var in
            IntHashtbl.replace freq var_idx
              ((try IntHashtbl.find freq var_idx with Not_found -> 0) + 1);
            cand := RegSet.add var !cand;
            if IntHashtbl.find freq var_idx = preds_length then begin
              cand := RegSet.remove var !cand;
              take := RegSet.add var !take
            end)
          (wexit pred))
      (Loop.Dom.predecessors block);
    let dists = M.next_use_distances.at_block (uid block) in
    let cand = List.sort (compare dists) (RegSet.elements !cand) in
    RegSet.(union !take (of_list (CCList.take (M.k - cardinal !take) cand)))

  let rec get_loop_nodes (node : Loop.Dom.position) : Loop.PositionSet.t =
    let nodes = Loop.loop_nodes.(node) in
    let add_loop_node node acc =
      if Loop.PositionSet.mem node Loop.loop_headers then
        Loop.PositionSet.(union (get_loop_nodes node) (add node acc))
      else Loop.PositionSet.add node acc
    in
    Loop.PositionSet.fold add_loop_node nodes (Loop.PositionSet.singleton node)

  let init_loop_header (block : Loop.Dom.position) =
    let loop = get_loop_nodes block in
    Logs.debug (fun m ->
        m "Loop nodes: %s\n"
          ([%show: G.label option list]
             (Loop.PositionSet.elements loop
             |> List.map Loop.Dom.label_of_position)));
    let alive = M.liveness.live_in (uid block) in
    Logs.debug (fun m ->
        m "Alive: %s\n" ([%show: G.regs] (RegSet.elements alive)));
    let used_in_loop =
      Loop.PositionSet.fold
        (fun node -> RegSet.union (M.liveness.used_in_block (uid node)))
        loop RegSet.empty
    in
    Logs.debug (fun m ->
        m "Used in loop: %s\n" ([%show: G.regs] (RegSet.elements used_in_loop)));
    let cand = RegSet.inter alive used_in_loop in
    Logs.debug (fun m ->
        m "Cand: %s\n" ([%show: G.regs] (RegSet.elements cand)));
    let dists = M.next_use_distances.at_block (uid block) in
    let max_pressure =
      Loop.PositionSet.fold
        (fun node -> max (M.liveness.max_register_pressure (uid node)))
        loop 0
    in
    Logs.debug (fun m -> m "Max pressure: %d\n" max_pressure);
    if RegSet.cardinal cand < M.k then begin
      let live_through = RegSet.diff alive cand in
      Logs.debug (fun m ->
          m "Live through: %s\n"
            ([%show: G.regs] (RegSet.elements live_through)));
      let free_loop =
        min
          (M.k - RegSet.cardinal cand)
          (M.k - (max_pressure - RegSet.cardinal live_through))
      in
      let live_through =
        List.sort (compare dists) (RegSet.elements live_through)
      in
      let cand =
        RegSet.(union cand (of_list (CCList.take free_loop live_through)))
      in
      Logs.debug (fun m ->
          m "Final Cand: %s\n" ([%show: G.regs] (RegSet.elements cand)));
      cand
    end
    else
      let cand = List.sort (compare dists) (RegSet.elements cand) in
      RegSet.of_list (CCList.take M.k cand)

  type min_state = {
    w : RegSet.t;
    s : RegSet.t;
  }

  type spill_state = {
    select_state : State.t;
    spill_mapping : Target.operand IntHashtbl.t;
    copies : G.Target.reg RegHashtbl.t;
  }

  let init (state : State.t) =
    {
      select_state = state;
      spill_mapping = IntHashtbl.create Utils.hashtbl_size;
      copies = RegHashtbl.create Utils.hashtbl_size;
    }

  open struct
    let get_slot (state : spill_state) v =
      let id = Target.index v in
      try IntHashtbl.find state.spill_mapping id
      with Not_found ->
        let slot = state.select_state.new_stack_slot 8 in
        IntHashtbl.add state.spill_mapping id slot;
        slot
  end

  let spill (state : spill_state) v =
    (* todo: only spill if no existing spill that dominates the current block *)
    Target.mov ~dest:(get_slot state v) ~src:(Target.reg v)

  let is_spilled (state : spill_state) v =
    IntHashtbl.mem state.spill_mapping (Target.index v)

  let reload (state : spill_state) v =
    try
      let slot = IntHashtbl.find state.spill_mapping (Target.index v) in
      let v' = state.select_state.fresh_vreg M.reg_class in
      RegHashtbl.add state.copies v v';
      Target.mov ~dest:(Target.reg v') ~src:slot
    with Not_found ->
      failwith
      @@ Format.asprintf "Couldn't find spill slot for %a" Target.pp_reg v

  let limit ~add_spills (state : spill_state) ({ w; s } : min_state)
      (block_uid : G.uid) (instr_num : int) (head : G.head) (m : int) :
      G.head * min_state =
    let dists = M.next_use_distances.at_instruction block_uid instr_num in
    Logs.debug (fun m ->
        let pp_sep fmt () = Format.fprintf fmt ", " in
        let pp_print_tuple fmt (a, b) =
          Format.fprintf fmt "%d -> %a" a (Format.pp_print_option CCInt.pp) b
        in
        m "Distances: %a\n"
          Format.(pp_print_list ~pp_sep pp_print_tuple)
          (List.map
             (fun v -> (Target.index v, IntMap.find_opt (Target.index v) dists))
             (RegSet.elements w)));
    let w = List.sort (compare dists) (RegSet.elements w) in
    let head, s =
      List.fold_left
        (fun (head, s) v ->
          let head =
            if
              (not (RegSet.mem v s))
              && (not (infinite_distance v dists))
              && add_spills
            then begin
              Logs.debug (fun m -> m "Spilling %a\n" Target.pp_reg v);
              G.Head (head, Instruction (spill state v))
            end
            else head
          in
          (head, RegSet.remove v s))
        (head, s) (CCList.drop m w)
    in
    let w = RegSet.of_list (CCList.take m w) in
    (head, { w; s })

  let min_algorithm ~add_spills (state : spill_state) (zblock : G.zblock)
      ({ w; s } : min_state) : G.zblock * min_state =
    let uid, w =
      match G.first zblock with
      | G.Entry -> (G.entry_uid, w)
      | G.Label ((uid, _), info) -> (uid, RegSet.(union w (of_list info.args)))
    in
    let rec go instr_num w s = function
      | head, G.Tail (Instruction instr, tail) ->
        let r = RegSet.diff (Target.uses instr) w in
        (* todo: just use RegSet.union r ? *)
        let w, s =
          RegSet.fold
            (fun use (w, s) -> (RegSet.add use w, RegSet.add use s))
            r (w, s)
        in
        Logs.debug (fun m ->
            m "W after adding uses in block %d: %s\n"
              G.(id (zip zblock))
              ([%show: G.regs] (RegSet.elements w)));
        let head, { w; s } =
          limit ~add_spills state { w; s } uid instr_num head M.k
        in
        let head = G.Head (head, Instruction instr) in
        (* add reloads for vars in r *)
        let head =
          if add_spills then
            RegSet.fold
              (fun var head ->
                Logs.debug (fun m -> m "Reloading %a\n" Target.pp_reg var);
                G.Head (head, Instruction (reload state var)))
              r head
          else head
        in
        let w = RegSet.union w (Target.defs instr) in
        let next_defs =
          match tail with
          | G.Tail (Instruction next, _) -> RegSet.cardinal (Target.defs next)
          | Last _ -> 0
        in
        (* provide room for definitions of next instruction *)
        (* measured from previous instruction because the next instruction's
           uses don't matter when writing to result registers *)
        let head, { w; s } =
          limit ~add_spills state { w; s } uid (instr_num + 1) head
            (M.k - next_defs)
        in
        go (instr_num + 1) w s (head, tail)
      | head, G.Last l ->
        let handle_instruction instr =
          let r = RegSet.diff (Target.uses instr) w in
          let w, s =
            RegSet.fold
              (fun use (w, s) -> (RegSet.add use w, RegSet.add use s))
              r (w, s)
          in
          limit ~add_spills state { w; s } uid instr_num head M.k
        in
        let head, min_state =
          match l with
          | G.Exit -> (head, { w; s })
          | Branch (i, _) -> handle_instruction i
          | CBranch (i, _, _) -> handle_instruction i
          | Return i -> handle_instruction i
        in
        ((head, G.Last l), min_state)
    in
    go 0 w s zblock

  let spill ?(args = []) (state : spill_state) (graph : G.graph) : G.graph =
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
      let zblock, graph = G.focus (uid pred) graph in
      let head, last = G.goto_end zblock in
      let insert_instr f var head = G.Head (head, Instruction (f var)) in
      let head =
        RegSet.fold
          (fun v head ->
            if is_spilled state v then insert_instr (reload state) v head
            else head)
          reloads head
      in
      let head = RegSet.fold (insert_instr (spill state)) spills head in
      G.unfocus ((head, Last last), graph)
    in
    let spill_block (state : spill_state) (graph : G.graph) (block_uid : G.uid)
        : G.graph =
      let pos = Loop.Dom.position_of_uid block_uid in
      let w_entry =
        if Loop.PositionSet.mem pos Loop.loop_headers then init_loop_header pos
        else if block_uid = G.entry_uid then RegSet.of_list args
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
      let all_processed =
        List.for_all (fun pred -> processed.(pred)) (Loop.Dom.predecessors pos)
      in
      let graph =
        Loop.Dom.predecessors pos
        |> List.filter (fun pred -> processed.(pred))
        |> List.fold_left (insert_coupling pos) graph
      in
      Logs.debug (fun m ->
          m "Block %d all processed: %b\n" block_uid all_processed);
      state.select_state.curr_block := block_uid;
      let zblock, graph = G.focus block_uid graph in
      let zblock, { w = w_exit; s = s_exit } =
        min_algorithm ~add_spills:all_processed state zblock
          { w = w_entry; s = s_entry }
      in
      (* save w_exit and s_exit for block id *)
      processed.(pos) <- true;
      saved_w_exit.(pos) <- w_exit;
      saved_s_exit.(pos) <- s_exit;
      let graph = G.unfocus (zblock, graph) in
      let fix_loop_header graph succ =
        (* update s_entry and rerun min algorithm to insert spills *)
        saved_s_entry.(succ) <-
          RegSet.(
            inter
              (union saved_s_entry.(succ) saved_s_exit.(pos))
              saved_w_entry.(succ));
        let zblock, graph = G.focus (uid succ) graph in
        let zblock, _ =
          min_algorithm ~add_spills:true state zblock
            { w = saved_w_entry.(succ); s = saved_s_entry.(succ) }
        in
        let graph = G.unfocus (zblock, graph) in
        insert_coupling succ graph pos
      in
      Loop.Dom.successors pos
      |> List.filter (fun succ -> processed.(succ))
      |> List.fold_left fix_loop_header graph
    in
    (* todo: can this be replaced with iterating from 0 to Loop.Dom.size-1? *)
    let rpo = G.reverse_postorder_dfs graph in
    List.fold_left
      (fun graph block -> spill_block state graph G.(idd (block_label block)))
      graph rpo
end

module X86 = struct
  module NextUseDistances =
    NextUseDistances.Make (X86.Target) (X86.Cfg) (X86.Flow)
  module Liveness = Liveness.Make (X86.Target) (X86.Cfg) (X86.Flow)
  module Make = Make (X86.Target) (X86.Cfg) (Select_x86.State) (Liveness)

  let spill_helper ?(args = [])
      (module Loop : Loopnesting.S
        with type Dom.label = X86.Cfg.label
         and type Dom.position = int
         and type Dom.uid = int) state cfg =
    let module NextUseDistances = NextUseDistances (Loop) in
    let next_use_distances = NextUseDistances.calc cfg in
    let liveness = Liveness.calc cfg in
    let module Spill' =
      Make (Loop) (NextUseDistances)
        (struct
          let reg_class = X86.Target.Int
          let k = 16
          let next_use_distances = next_use_distances
          let liveness = liveness
        end) in
    let spill_state = Spill'.init state in
    let cfg = Spill'.spill ~args spill_state cfg in
    let module Reconstruct = Reconstruct.Make (X86.Target) (X86.Cfg) (Loop.Dom)
    in
    let reconstruct_copies reg _ graph =
      let copies = Spill'.RegHashtbl.find_all spill_state.copies reg in
      let def_blocks =
        List.map
          (fun r ->
            Deadcode.IntHashtbl.find spill_state.select_state.vreg_block
              (X86.Target.index r))
          (reg :: copies)
      in
      Reconstruct.reconstruct
        (fun () -> spill_state.select_state.fresh_vreg Int)
        (Spill'.RegSet.singleton reg)
        (Spill'.RegSet.of_list copies)
        def_blocks graph
    in
    Spill'.RegHashtbl.fold reconstruct_copies spill_state.copies cfg
end
