open Alcotest
open Baby_pascal

type reg_mapping = (X86.Target.physical_reg * bool) list

let get_vreg vreg =
  match vreg with
  | X86.Target.Virtual vreg -> vreg
  | _ -> failwith "Not a virtual register"

let setup_register_shuffle ~(regs : X86.Target.reg array)
    ~(extra_curr_live : reg_mapping) ~(uses : reg_mapping) ~(defs : reg_mapping)
    ~(extra_clobbered_regs : reg_mapping) =
  let cfg = X86.Cfg.empty in
  let extra = X86.Cfg.precalculate_edges cfg in
  let module Dom = Dominator.Make (X86.Cfg) ((val extra)) in
  let select_state = Select_x86.State.init () in
  let block_execution_frequency _uid = 1. in
  let num_vregs =
    List.(
      length extra_curr_live + length uses + length defs
      + length extra_clobbered_regs)
  in
  let uid, instr_num = (2, 5) in
  select_state.curr_block := uid;
  let vregs = Array.init num_vregs (fun _ -> select_state.fresh_vreg Int) in
  let live_through = Utils.IntHashtbl.create num_vregs in
  let dies _uid = function
    | X86.Target.Virtual vreg ->
      Some
        (if Utils.IntHashtbl.mem live_through vreg.id then instr_num + 1
         else instr_num)
    | _ -> None
  in
  let liveness =
    X86.Target.
      {
        Spill.Liveness.live_in = (fun _ -> RegSet.empty);
        live_out = (fun _ -> RegSet.empty);
        used_in_block = (fun _ -> RegSet.empty);
        dies;
        max_register_pressure = (fun _ -> 0);
      }
  in
  let open Regalloc in
  let state =
    init_state ~select_state ~regs ~block_execution_frequency ~liveness
      (module Dom)
  in
  let idx phys = find_reg_index regs (X86.Target.Physical phys) in
  let set_reg idx = function
    | X86.Target.Virtual vreg ->
      vreg.reg <- regs.(idx);
      state.reg_current_var.(idx) <- Some vreg;
      state.reg_current_pref.(idx) <- state.preferences.(vreg.id).(idx)
    | _ -> failwith "Register not virtual"
  in
  let next_vreg =
    let c = ref (-1) in
    fun () ->
      incr c;
      !c
  in
  let setup_occupied (reg, is_live_through) =
    let vreg = vregs.(next_vreg ()) in
    CCBV.set state.occupied (idx reg);
    set_reg (idx reg) vreg;
    if is_live_through then
      Utils.IntHashtbl.replace live_through (X86.Target.index vreg) true;
    X86.Target.Reg vreg
  in
  let setup_constrained (reg, is_live_through) =
    let vreg = vregs.(next_vreg ()) in
    ignore @@ X86.Target.constrained reg vreg;
    if is_live_through then
      Utils.IntHashtbl.replace live_through (X86.Target.index vreg) true;
    X86.Target.Reg vreg
  in
  let srcs = CCVector.create () in
  let dests = CCVector.create () in
  List.iter (fun t -> ignore (setup_occupied t)) extra_curr_live;
  List.iter (fun t -> CCVector.push srcs (setup_occupied t)) uses;
  List.iter (fun t -> CCVector.push dests (setup_constrained t)) defs;
  List.iter
    (fun t -> CCVector.push dests (setup_constrained t))
    extra_clobbered_regs;
  let old_vregs =
    Array.init (Array.length vregs) (fun i -> (get_vreg vregs.(i)).reg)
  in
  let instr =
    X86.Target.pcopy ~dests:(CCVector.to_list dests)
      ~srcs:(CCVector.to_list srcs)
  in
  let head, instr =
    enforce_constraints state uid instr_num instr (X86.Cfg.First Entry)
  in
  (old_vregs, vregs, X86.Cfg.Head (head, Instruction instr))

let test_pcopy_instr ~regs head =
  let dummy_reg = (-100, X86.Target.Int, "dummy") in
  let module Sequentialize =
    Seqpcopy.Make
      (X86.Cfg)
      (struct
        include X86.SeqpcopyRequirements
        let temp = Target.Reg (Physical dummy_reg)
      end) in
  let rec expand_pcopies tail = function
    | X86.Cfg.First _ -> tail
    | X86.Cfg.Head (head, Instruction instr) ->
      let instr =
        instr
        |> X86.Target.map_uses X86.Target.to_colored
        |> X86.Target.map_defs (function
          | X86.Target.Reg (Virtual { reg_constr = UsePhysical phys; _ }) ->
            Reg regs.(Regalloc.find_reg_index regs (Physical phys))
          | op -> op)
      in
      let tail = Sequentialize.parallel_copy_instr instr tail in
      expand_pcopies tail head
  in
  let tail = expand_pcopies (Last Exit) head in
  Format.printf "Expanded pcopies: %a\n" X86.Cfg.pp_tail tail;
  let init_state = ref X86.Target.RegMap.empty in
  Array.iteri
    (fun v reg -> init_state := X86.Target.RegMap.add reg v !init_state)
    regs;
  let init_state =
    X86.Target.RegMap.add (Physical dummy_reg) (-1) !init_state
  in
  let update_state state instr =
    let go state = function
      | X86.Target.Reg src, X86.Target.Reg dest ->
        Format.printf "Setting: %a to %d at %a\n" X86.Target.pp_reg dest
          (X86.Target.RegMap.find src state)
          X86.Target.pp_reg src;
        X86.Target.RegMap.(add dest (find src state) state)
      | _ -> failwith "Invalid srcs and dests"
    in
    List.(fold_left go state (combine instr.X86.Target.uses instr.defs))
  in
  let rec interpret_moves state = function
    | X86.Cfg.Tail (Instruction i, rest) ->
      interpret_moves (update_state state i) rest
    | X86.Cfg.Last _ -> state
  in
  let result_state = interpret_moves init_state tail in
  (init_state, result_state)

let clobber_constrained constrained state =
  fst
  @@ List.fold_left
       (fun (state, v) reg -> (X86.Target.RegMap.add reg v state, v - 1))
       (state, -1) constrained

let check_result_state ~extra_curr_live ~uses ~defs ~extra_clobbered_regs
    ~old_vregs ~vregs ~init_state ~result_state =
  (* Check that values of the uses original registers are in the constrained registers *)
  let check_use (use, _) (def, _) =
    check int
      (Format.asprintf "Checking that %a was moved to %a" X86.Target.pp_reg
         (Physical use) X86.Target.pp_reg (Physical def))
      (X86.Target.RegMap.find (Physical use) init_state)
      (X86.Target.RegMap.find (Physical def) result_state)
  in
  List.iter2 check_use uses defs;
  (* Then clobber all the constrained defs *)
  let result_state =
    clobber_constrained
      (List.map
         (fun (phys, _) -> X86.Target.Physical phys)
         extra_clobbered_regs)
      result_state
  in
  (* Then check that the live through values before the instruction
       are still there after substitution *)
  let live_throughs =
    extra_curr_live @ uses
    |> List.mapi (fun i (_, live_through) -> (i, live_through))
    |> List.filter_map (fun (i, live_through) ->
        if live_through then Some i else None)
  in
  let check_live_through vreg =
    let vreg' = get_vreg vreg in
    check int
      (Format.asprintf
         "Checking that vreg %d was moved from %a to %a and is still live \
          through"
         vreg'.id X86.Target.pp_reg old_vregs.(vreg'.id) X86.Target.pp_reg
         vreg'.reg)
      (X86.Target.RegMap.find old_vregs.(vreg'.id) init_state)
      (X86.Target.RegMap.find vreg'.reg result_state)
  in
  List.iter check_live_through (List.map (fun i -> vregs.(i)) live_throughs)

(* [ rax; rbx; rcx; rdx; rsi; rdi; rsp; rbp; r8; r9; r10; r11; r12; r13; r14; r15; ] *)
let regs =
  X86.Regs.int_regs
  |> List.map (fun phys -> X86.Target.Physical phys)
  |> Array.of_list

(* let idx phys = Regalloc.find_reg_index regs (X86.Target.Physical phys)
let fresh_vreg ~id ~phys =
  X86.Target.Virtual
    {
      id;
      reg_class = Int;
      reg_constr = UsePhysical phys;
      reg = regs.(idx phys);
    } *)

let pick ?(regs = regs) =
  let regs = Array.copy regs in
  fun num ->
    CCArray.shuffle regs;
    Array.to_list regs |> CCList.take num

(* Invariants:

   length(defs) = length(uses)
   intersect(uses, extra_curr_live) = {}
   total_live_through = length(regs) - length(union(defs, extra_clobbered_regs))
   length(extra_curr_live) <= total_live_through
   length(extra_curr_live) + count(is_live_through, uses) = total_live_through
*)
let rec randomized_register_shuffle_test () =
  let get_random () = CCRandom.(run (int_range 1 (Array.length regs))) in
  let extra_curr_live = pick (get_random ()) in
  let extra_clobbered_regs = pick (get_random ()) in
  let uses =
    pick
      ~regs:
        (Array.of_list
           X86.Target.RegSet.(
             to_list
               (diff (of_list (Array.to_list regs)) (of_list extra_curr_live))))
      (get_random ())
  in
  let defs = pick (List.length uses) in
  let num_live_through =
    Array.length regs
    - X86.Target.RegSet.(
        cardinal (union (of_list defs) (of_list extra_clobbered_regs)))
  in
  if
    List.length uses = List.length defs
    && List.length extra_curr_live <= num_live_through
  then begin
    let get_physical = function
      | X86.Target.Physical p -> p
      | _ -> failwith "Not a physical register"
    in
    let num_live_uses = num_live_through - List.length extra_curr_live in
    let uses =
      let live, non_live = CCList.take_drop num_live_uses uses in
      let arr =
        Array.of_list
        @@ List.map (fun l -> (get_physical l, true)) live
        @ List.map (fun l -> (get_physical l, false)) non_live
      in
      CCArray.shuffle arr;
      Array.to_list arr
    in
    let extra_curr_live =
      List.map (fun l -> (get_physical l, true)) extra_curr_live
    in
    let extra_clobbered_regs =
      List.map (fun l -> (get_physical l, true)) extra_clobbered_regs
    in
    let defs = List.map (fun l -> (get_physical l, true)) defs in
    let pp_phys fmt (phys, live_through) =
      if live_through then
        Format.fprintf fmt "!%a" X86.Target.pp_reg (Physical phys)
      else Format.fprintf fmt "%a" X86.Target.pp_reg (Physical phys)
    in
    let test_name =
      let pp_sep fmt () = Format.fprintf fmt "," in
      let pp_phys_list = Format.pp_print_list ~pp_sep pp_phys in
      Format.asprintf "live %a uses %a defs %a clob %a" pp_phys_list
        extra_curr_live pp_phys_list uses pp_phys_list defs pp_phys_list
        extra_clobbered_regs
    in
    test_case test_name `Quick @@ fun () ->
    Format.printf "Test: %s\n" test_name;
    let old_vregs, vregs, head =
      setup_register_shuffle ~regs ~extra_curr_live ~uses ~defs
        ~extra_clobbered_regs
    in
    Format.printf "Head: %a\n" X86.Cfg.pp_head head;
    let init_state, result_state = test_pcopy_instr ~regs head in
    check_result_state ~extra_curr_live ~uses ~defs ~extra_clobbered_regs
      ~old_vregs ~vregs ~init_state ~result_state
  end
  else randomized_register_shuffle_test ()

let test_register_shuffle1 () =
  (* vregs 0, 1, 2 are live through but not in the uses or defs of the instruction *)
  let extra_curr_live = X86.Regs.[ (rdi, true); (rsi, true); (rdx, true) ] in
  (* vregs 3, 4, 5, 6 are the uses of the instruction in callee save registers
     3, 4, and 6 die at the instruction, but 5 is live through *)
  let uses =
    X86.Regs.[ (r12, false); (r13, false); (rbx, true); (r9, false) ]
  in
  (* vregs 7, 8, 9, 10 are constrained to rdi, rsi, rdx, rcx *)
  let defs = List.map (fun r -> (r, true)) X86.Regs.[ rdi; rsi; rdx; rcx ] in
  (* vregs 11, 12, 13, 14, 15, 16, 17, 18, 19 are the constrained defs of the instruction
     the def for rax lives through the instruction but the rest die *)
  let extra_clobbered_regs =
    X86.Regs.
      [
        (rax, true);
        (rcx, false);
        (r8, false);
        (r9, false);
        (r10, false);
        (r11, false);
        (rdx, false);
        (rsi, false);
        (rdi, false);
      ]
  in
  let old_vregs, vregs, head =
    setup_register_shuffle ~regs ~extra_curr_live ~uses ~defs
      ~extra_clobbered_regs
  in
  let expected_instr =
    X86.Target.pcopy
      ~dests:
        (List.map
           (fun r -> X86.Target.Reg (Physical r))
           X86.Regs.[ r13; r12; rsp; rdi; rsi; rdx; rcx ])
      ~srcs:
        (List.map
           (fun r -> X86.Target.Reg (Physical r))
           X86.Regs.[ rsi; rdi; rdx; r12; r13; rbx; r9 ])
  in
  let init_state, result_state = test_pcopy_instr ~regs head in
  check_result_state ~extra_curr_live ~uses ~defs ~extra_clobbered_regs
    ~old_vregs ~vregs ~init_state ~result_state;
  check
    X86.Cfg.(testable pp_head equal_head)
    "Check result instruction" head
    (X86.Cfg.Head (First Entry, Instruction expected_instr))

let _ =
  let _ = Random.set_state (Random.get_state ()) in
  Logs.set_reporter (Logs_fmt.reporter ());
  Logs.set_level (Some Logs.Debug);
  let randomized =
    List.init 100 (fun _ -> randomized_register_shuffle_test ())
  in
  run "Test_register_allocation"
    [
      ( "Tests_enforce_constraints",
        test_case "simple example" `Quick test_register_shuffle1 :: randomized
      );
    ]
