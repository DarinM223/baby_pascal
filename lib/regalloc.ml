module RegSet = Spill.Liveness.RegSet

module Weights = struct
  let use_factor = 1.
  let def_factor = 1.
  let neighbor_factor = 0.2
  let aff_should_be_same = 0.5
  let aff_phi = 1.
end

type state = {
  regs : X86.Target.reg array;
  num_vars : int;
  processed : bool array;
  block_execution_frequency : X86.Cfg.uid -> float;
  preferences : float array array;
  (* initially -1 if no variable for register *)
  reg_current_var : int array;
  (* initially 0 *)
  reg_current_pref : float array;
  liveness : Spill.Liveness.t;
  dom :
    (module Dominator.S
       with type label = X86.Cfg.label
        and type uid = X86.Cfg.uid
        and type position = int);
}

let get_register state uid var occupied head : int * float * X86.Cfg.head =
  let preferences =
    state.preferences.(X86.Target.index var)
    |> Array.mapi (fun i pref -> (i, pref))
  in
  Array.sort
    (fun (_, pref1) (_, pref2) -> Float.compare pref1 pref2)
    preferences;
  let exception Reg of int * float * X86.Cfg.head in
  let exception Break of int * float in
  try
    for i = Array.length preferences - 1 downto 0 do
      let reg, pref = preferences.(i) in
      if not (CCBV.get occupied reg) then raise (Reg (reg, pref, head));
      let ovar = state.reg_current_var.(reg) in
      let preferences =
        Array.mapi (fun i pref -> (i, pref)) state.preferences.(ovar)
      in
      Array.sort
        (fun (_, pref1) (_, pref2) -> Float.compare pref1 pref2)
        preferences;
      try
        for i = Array.length preferences - 1 downto 0 do
          let oreg, opref = preferences.(i) in
          if not (CCBV.get occupied oreg) then
            raise (Break (oreg, opref -. state.reg_current_pref.(oreg)))
        done
      with Break (oreg, other_win) ->
        if i + 1 < Array.length preferences then
          let _, next_pref = preferences.(i + 1) in
          let win = next_pref -. pref in
          if win +. other_win > state.block_execution_frequency uid then
            let mov =
              X86.Target.mov
                ~dest:(Reg state.regs.(oreg))
                ~src:(Reg state.regs.(reg))
            in
            let head = X86.Cfg.Head (head, Instruction mov) in
            raise (Reg (reg, pref, head))
    done;
    failwith "get_register: couldn't find non-occupied register"
  with Reg (reg, pref, head) -> (reg, pref, head)

let enforce_constraints _state _instr = ()

let implement_phi_copies _state ~src:_ ~dest:_ = ()

let dies state uid a instr_num =
  match state.liveness.dies uid a with
  | Some num when num <= instr_num -> true
  | _ -> false

let color_block state ((first, tail) as block : X86.Cfg.block) : X86.Cfg.block =
  let uid = X86.Cfg.id block in
  let occupied = CCBV.create ~size:(Array.length state.regs) false in
  let phis =
    match first with
    | X86.Cfg.Entry -> []
    | X86.Cfg.Label (_, info) -> info.args
  in
  let head =
    List.fold_left
      (fun head -> function
        | X86.Target.Virtual phi' as phi ->
          let reg, pref, head = get_register state uid phi occupied head in
          phi'.reg <- state.regs.(reg);
          state.reg_current_var.(reg) <- phi'.id;
          state.reg_current_pref.(reg) <- pref;
          CCBV.set occupied reg;
          head
        | _ -> head)
      (X86.Cfg.First first) phis
  in
  let handle_instruction instr_num head instr =
    enforce_constraints state instr;
    X86.Target.RegSet.iter
      (function
        | X86.Target.Virtual a' as a when dies state uid a instr_num ->
          let reg = X86.Target.index a'.reg in
          state.reg_current_var.(reg) <- -1;
          state.reg_current_pref.(reg) <- 0.;
          CCBV.reset occupied reg
        | _ -> ())
      (X86.Target.uses instr);
    X86.Target.RegSet.fold
      (function
        | X86.Target.Virtual r' as r ->
          fun head ->
            let reg, pref, head = get_register state uid r occupied head in
            r'.reg <- state.regs.(reg);
            state.reg_current_var.(reg) <- r'.id;
            state.reg_current_pref.(reg) <- pref;
            CCBV.set occupied reg;
            head
        | _ -> fun head -> head)
      (X86.Target.defs instr) head
  in
  let rec go instr_num head = function
    | X86.Cfg.Tail (Instruction instr, tail) ->
      let head = handle_instruction instr_num head instr in
      go (instr_num + 1) (X86.Cfg.Head (head, Instruction instr)) tail
    | X86.Cfg.Last l ->
      (* todo: propagate branch args to the affinity chunk *)
      let head =
        match l with
        | X86.Printer.Exit -> head
        | X86.Printer.Branch (i, _) -> handle_instruction instr_num head i
        | X86.Printer.CBranch (i, _, _) -> handle_instruction instr_num head i
        | X86.Printer.Return i -> handle_instruction instr_num head i
      in
      (head, X86.Cfg.Last l)
  in
  let block = X86.Cfg.zip (go 0 head tail) in
  let module Dom = (val state.dom) in
  let pos = Dom.position_of_uid uid in
  state.processed.(pos) <- true;
  List.iter
    (fun pred ->
      if state.processed.(pred) then
        implement_phi_copies state ~src:pred ~dest:pos)
    (Dom.predecessors pos);
  List.iter
    (fun succ ->
      (* todo: use block.succs[0] instead *)
      if state.processed.(succ) then
        implement_phi_copies state ~src:pos ~dest:succ)
    (Dom.successors pos);
  block

let build_preferences state graph : float array array =
  let preferences =
    Array.init_matrix state.num_vars (Array.length state.regs) (fun _ _ -> 0.)
  in
  let rec handle_operand ?(def = false) uid live = function
    | X86.Target.(Reg (Virtual { id; reg_constr = ReuseOperand reg; _ }))
      when def ->
      (* add preferences to use variable when there is a reuse operand def *)
      let op = X86.Target.index reg in
      for i = 0 to Array.length preferences.(op) - 1 do
        preferences.(op).(i) <- preferences.(op).(i) +. preferences.(id).(i)
      done
    | X86.Target.(Reg (Virtual { id; reg_constr = UsePhysical (reg, _, _); _ }))
      ->
      let weight = state.block_execution_frequency uid in
      let penalty =
        weight *. if def then Weights.def_factor else Weights.use_factor
      in
      (* give penalties to all registers that are not the constrained register. *)
      for i = 0 to Array.length preferences.(id) - 1 do
        if i <> reg then preferences.(id).(i) <- preferences.(id).(i) -. penalty
      done;
      let penalty = penalty *. Weights.neighbor_factor in
      (* give penalties to all other live variables for the constrained register *)
      CCBV.iter_true live (fun live ->
          if live <> id then
            preferences.(live).(reg) <- preferences.(live).(reg) -. penalty)
    | X86.Target.Label (_, ops) -> List.iter (handle_operand uid live) ops
    | _ -> ()
  in
  let handle_instruction uid live (instr : X86.Target.instr) =
    List.iter (handle_operand ~def:true uid live) instr.defs;
    let defs =
      X86.Target.defs instr |> X86.Target.RegSet.to_list
      |> List.map X86.Target.index |> CCBV.of_list
    in
    CCBV.diff_into ~into:live defs;
    List.iter (handle_operand uid live) instr.uses;
    let uses =
      X86.Target.uses instr |> X86.Target.RegSet.to_list
      |> List.map X86.Target.index |> CCBV.of_list
    in
    CCBV.union_into ~into:live uses
  in
  let go_block block =
    let uid = X86.Cfg.id block in
    let live_out = state.liveness.live_out uid in
    let live =
      CCBV.of_list
        (List.map X86.Target.index (X86.Target.RegSet.to_list live_out))
    in
    let head, last = X86.Cfg.(goto_end (unzip block)) in
    begin match last with
    | X86.Printer.Exit -> ()
    | X86.Printer.Branch (i, _) -> handle_instruction uid live i
    | X86.Printer.CBranch (i, _, _) -> handle_instruction uid live i
    | X86.Printer.Return i -> handle_instruction uid live i
    end;
    let rec go_head = function
      | X86.Cfg.Head (head, Instruction i) ->
        handle_instruction uid live i;
        go_head head
      | X86.Cfg.First _ -> () (* ignore phis *)
    in
    go_head head
  in
  let rpo = X86.Cfg.reverse_postorder_dfs graph in
  List.iter go_block rpo;
  preferences

let create_congruence_class state classes graph block =
  let live =
    let live_out = state.liveness.live_out (X86.Cfg.id block) in
    CCBV.of_list
      (List.map X86.Target.index (X86.Target.RegSet.to_list live_out))
  in
  let liveness_transfer instr =
    let defs =
      X86.Target.defs instr |> X86.Target.RegSet.to_list
      |> List.map X86.Target.index |> CCBV.of_list
    in
    let uses =
      X86.Target.uses instr |> X86.Target.RegSet.to_list
      |> List.map X86.Target.index |> CCBV.of_list
    in
    CCBV.diff_into ~into:live defs;
    CCBV.union_into ~into:live uses
  in
  let handle_jump_arg succ args i arg =
    let succ = X86.Cfg.idd (Some succ) in
    let live = state.liveness.live_in succ in
    let check_interferes v =
      Unionfind.equal_repr
        (Unionfind.find classes (X86.Target.index v))
        (Unionfind.find classes (X86.Target.index arg))
    in
    (* interferes if anything in live_in of block successor has the same set representative as jump arg
       or if other args in jump has same set representative as jump arg *)
    let interferes =
      RegSet.exists check_interferes live
      || args
         |> List.filter_map (function
           | X86.Target.Reg r when r <> arg -> Some r
           | _ -> None)
         |> List.exists check_interferes
    in
    (* if no interference, merge jump arg and successor phi classes and add preferences to set representative *)
    if not interferes then
      let phi =
        match X86.Cfg.(first (fst (focus succ graph))) with
        | X86.Cfg.Entry ->
          failwith "create_congruence_class: jump with arguments to entry block"
        | X86.Cfg.Label (_, info) ->
          begin match List.nth_opt info.args i with
          | Some phi -> phi
          | None ->
            failwith "create_congruence_class: jump has different arity to phis"
          end
      in
      let arg_repr = Unionfind.find classes (X86.Target.index arg) in
      let phi_repr = Unionfind.find classes (X86.Target.index phi) in
      let merged_repr = Unionfind.union classes arg_repr phi_repr in
      let other_repr =
        if Unionfind.equal_repr merged_repr phi_repr then arg_repr else phi_repr
      in
      let merged = state.preferences.(Unionfind.to_int merged_repr) in
      let other = state.preferences.(Unionfind.to_int other_repr) in
      for r = 0 to Array.length state.regs - 1 do
        merged.(r) <- merged.(r) +. other.(r)
      done
  in
  let handle_jump instr =
    List.iter
      (function
        | X86.Target.Label (succ, args) ->
          List.iteri
            (fun i -> function
              | X86.Target.Reg r -> handle_jump_arg succ args i r
              | _ -> ())
            args
        | _ -> ())
      instr.X86.Target.uses
  in
  let head, last = X86.Cfg.(goto_end (unzip block)) in
  begin match last with
  | X86.Printer.Exit -> ()
  | X86.Printer.Branch (instr, _) ->
    handle_jump instr;
    liveness_transfer instr
  | X86.Printer.CBranch (instr, _, _) ->
    handle_jump instr;
    liveness_transfer instr
  | X86.Printer.Return instr -> liveness_transfer instr
  end;
  let handle_reuse_operand_def = function
    | X86.Target.(Reg (Virtual { id; reg_constr = ReuseOperand op; _ })) ->
      let op = X86.Target.index op in
      let interferes = ref false in
      let exception Break in
      (* if any current live variables has the same set representative as the reused operand then it interferes *)
      begin try
        CCBV.iter_true live @@ fun v ->
        if Unionfind.(equal_repr (find classes v) (find classes op)) then begin
          interferes := true;
          raise Break
        end
      with Break -> ()
      end;
      (* if no interference then merge classes for reuse operand def and use variables *)
      if not !interferes then
        ignore Unionfind.(union classes (find classes id) (find classes op))
    | _ -> ()
  in
  let rec go_head = function
    | X86.Cfg.First _ -> ()
    | X86.Cfg.Head (head, Instruction instr) ->
      List.iter handle_reuse_operand_def instr.defs;
      liveness_transfer instr;
      go_head head
  in
  go_head head

let set_congruence_prefs state classes v =
  let v_repr = Unionfind.(to_int (find classes v)) in
  if v <> v_repr then
    Array.blit state.preferences.(v_repr) 0 state.preferences.(v) 0
      (Array.length state.preferences.(v))

let combine_congruence_classes state graph =
  let classes = Unionfind.create state.num_vars in
  let rpo = X86.Cfg.reverse_postorder_dfs graph in
  List.iter (create_congruence_class state classes graph) rpo;
  Array.iteri
    (fun v _ -> set_congruence_prefs state classes v)
    state.preferences

let rec add_trace (module Dom : Dominator.S with type position = int) trace seen
    order block =
  if not seen.(block) then begin
    let best_pred =
      Dom.predecessors block
      |> List.filter (fun pred -> not (Dom.dominates block pred))
      |> List.fold_left
           (function
             | None -> fun pred -> Some pred
             | Some best ->
               fun pred ->
                 Some (if trace.(best) < trace.(pred) then pred else best))
           None
    in
    let order =
      match best_pred with
      | Some pred -> add_trace (module Dom) trace seen order pred
      | None -> order
    in
    seen.(block) <- true;
    block :: order
  end
  else order

let blockorder state =
  let module Dom = (val state.dom) in
  let trace = Array.make Dom.size 0. in
  for b = Dom.size - 1 downto 0 do
    let uid = X86.Cfg.idd (Dom.label_of_position b) in
    let t =
      List.fold_left
        (fun acc pred -> max acc trace.(pred))
        0. (Dom.predecessors b)
    in
    trace.(b) <- t +. state.block_execution_frequency uid
  done;
  let blocks = Array.init Dom.size (fun i -> i) in
  Array.sort (fun a b -> Float.compare trace.(a) trace.(b)) blocks;
  let seen = Array.make Dom.size false in
  List.rev @@ Array.fold_left (add_trace (module Dom) trace seen) [] blocks

let%expect_test "Nested loops register allocation" =
  let ast =
    let open Ast in
    [
      Assign ("i", Int 0);
      While
        ( Bop (Lt, Var "i", Int 100),
          [
            Assign ("j", Var "i");
            While
              ( Bop (Lt, Var "j", Int 100),
                [
                  Assign ("j", Bop (Add, Var "j", Int 1));
                  Assign ("i", Bop (Add, Var "i", Int 1));
                ] );
          ] );
    ]
  in
  let module F = Normalize.Fresh () in
  let cfg = Normalize.normalize F.fresh ast in
  let state = Select_x86.State.init () in
  let cfg = Select_x86.codegen_test_helper state [] cfg in
  let extra = X86.Cfg.precalculate_edges cfg in
  let module Extra = (val extra) in
  let module Dom = Dominator.Make (X86.Cfg) (Extra) in
  let module Loop = Loopnesting.Make (X86.Cfg) (Dom) in
  let module Freq = Execfreq.Make (X86.Cfg) (Loop) (X86.ExecfreqRequirements) in
  let next_use_distances = Spill.next_use_distances (module Loop) cfg in
  let liveness = Spill.Liveness.calc cfg in
  let module Spill =
    Spill.Make
      (Loop)
      (struct
        let k = 16
        let next_use_distances = next_use_distances
        let liveness = liveness
      end) in
  let spill_state = Spill.init state in
  let cfg = Spill.(spill spill_state cfg) in
  let block_execution_frequency uid = Freq.bfreq.(Extra.position_of_uid uid) in
  let regs = X86.Regs.int_regs |> Array.map (fun r -> X86.Target.Physical r) in
  let state =
    {
      regs;
      block_execution_frequency;
      liveness;
      dom = (module Dom);
      reg_current_var = Array.make (Array.length regs) (-1);
      reg_current_pref = Array.make (Array.length regs) 0.;
      processed = Array.make Extra.size false;
      (* block specific state, initialize for each block *)
      num_vars = 0;
      preferences = Array.make_matrix 0 0 0.;
    }
  in
  let go_block cfg pos =
    let uid = X86.Cfg.idd (Extra.label_of_position pos) in
    let zblock, cfg = X86.Cfg.focus uid cfg in
    (* todo: setup state for block *)
    let block = color_block state (X86.Cfg.zip zblock) in
    X86.Cfg.(unfocus (unzip block, cfg))
  in
  let cfg = List.fold_left go_block cfg (blockorder state) in
  Format.printf "%a" X86.Printer.pp_graph cfg;
  [%expect {||}]

(* type state = {
  regs : X86.Target.reg array;
  num_vars : int;
  processed : bool array;
  block_execution_frequency : X86.Cfg.uid -> float;
  preferences : float array array;
  (* initially -1 if no variable for register *)
  reg_current_var : int array;
  (* initially 0 *)
  reg_current_pref : float array;
  liveness : Spill.Liveness.t;
  dom :
    (module Dominator.S
       with type label = X86.Cfg.label
        and type uid = X86.Cfg.uid
        and type position = int);
} *)
