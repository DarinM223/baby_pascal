let compile_shared lower_isa program =
  let program = Check.check_program program in
  let module F = Normalize.Fresh () in
  let program =
    let open Ast in
    let normalize_decl globals = function
      | Function (f, ps, t, body) ->
        let globals, body = Normalize.normalize (module F) globals body in
        (globals, Function (f, ps, t, Normalize.set_return t f body))
      | Procedure (f, ps, body) ->
        let globals, body = Normalize.normalize (module F) globals body in
        (globals, Procedure (f, ps, body))
    in
    let globals, decls =
      List.fold_left_map normalize_decl program.globals program.decls
    in
    let globals, main = Normalize.normalize (module F) globals program.main in
    { globals; main; decls }
  in
  let rec round (module Dom : Dominator.S with type label = Normalize.Cfg.label)
      args cfg =
    let cfg, changed = Deadcode.M.deadcode cfg in
    let cfg, changed' =
      let block_args = Constprop.block_args cfg in
      Constprop.constprop block_args args cfg
    in
    let cfg, recalculate_dominators = Constprop.remove_empty_blocks cfg in
    (* Avoid recalculating dominators unless the previous passes changed it
       Dominators are currently used only at the block level, so only deleting
       blocks will require a recalculation. *)
    let dom =
      if recalculate_dominators then
        let extra = Normalize.Cfg.precalculate_edges cfg in
        let module Extra = (val extra) in
        let module Dom = Dominator.Make (Normalize.Cfg) (Extra) in
        (module Dom : Dominator.S with type label = Normalize.Cfg.label)
      else (module Dom)
    in
    let module Dom = (val dom) in
    let module Valuenumbering = Valuenumbering.Make (Dom) in
    let state = Valuenumbering.init_state () in
    let cfg = Valuenumbering.dvnt state (Lazy.force Dom.dominator_tree) cfg in
    if changed || changed' || state.changed then round (module Dom) args cfg
    else cfg
  in
  let lower_cfg f (args : (Ast.typ * string) list) cfg =
    let extra = Normalize.Cfg.precalculate_edges cfg in
    let module Extra = (val extra) in
    let module Dom = Dominator.Make (Normalize.Cfg) (Extra) in
    let a_orig = Construct.calc_a_orig cfg in
    let live = Construct.calc_live cfg in
    let cfg = Construct.insert_phis_pruned live (module Dom) a_orig cfg in
    let cfg = Construct.rename_variables (module Dom) cfg in
    let args = List.map (fun (typ, arg) -> (typ, (arg, 0))) args in
    Format.printf "===================================\n";
    Format.printf "%s's initial cfg:\n" f;
    Format.printf "===================================\n";
    Format.printf "%a\n" Normalize.Writer.pp_graph cfg;
    let cfg = round (module Dom) (List.map snd args) cfg in
    Format.printf "===================================\n";
    Format.printf "%s's cfg after optimization passes:\n" f;
    Format.printf "===================================\n";
    Format.printf "%a\n" Normalize.Writer.pp_graph cfg;
    let module Critedgesplit =
      Critedgesplit.Make (F) (Normalize.Cfg) (Extra)
        (struct
          module Target = Normalize.Target
          include Target
        end) in
    let cfg = Critedgesplit.split cfg in
    Format.printf "===================================\n";
    Format.printf "%s's cfg after critical edge split:\n" f;
    Format.printf "===================================\n";
    Format.printf "%a\n" Normalize.Writer.pp_graph cfg;
    let cfg = Undag.undag_graph cfg in
    Format.printf "===================================\n";
    Format.printf "%s's cfg after undag:\n" f;
    Format.printf "===================================\n";
    Format.printf "%a\n" Undag.Writer.pp_graph cfg;
    lower_isa ~f ~args ~cfg
  in
  let lower_decl = function
    | Ast.Function (f, args, ret, body) ->
      Ast.Function (f, args, ret, lower_cfg f (List.map CCPair.swap args) body)
    | Ast.Procedure (f, args, body) ->
      Ast.Procedure (f, args, lower_cfg f (List.map CCPair.swap args) body)
  in
  let decls = List.map lower_decl program.decls in
  let main = lower_cfg "main" [] program.main in
  { program with decls; main }

let write_global out { Ast.id; typ; value } =
  match value with
  (* write in .bss *)
  | Ast.Uninitialized ->
    Format.fprintf out ".bss\n.lcomm %s, %d\n" id (Ast.sizeof typ)
  (* write in .data *)
  | Ast.Initialized (ConstDouble f) ->
    Format.fprintf out ".data\n%s: .double %f\n" id f
  | Ast.Initialized (ConstInt i) ->
    Format.fprintf out ".data\n%s: .quad %d\n" id i
  | Ast.Initialized (ConstString s) ->
    Format.fprintf out ".data\n%s: .asciz \"%s\"\n" id s
  | Ast.Initialized (ConstArray _a) ->
    (* todo: recursively lower elements inside of an array
           so an array of arrays or strings would have the elements
           lowered first *)
    failwith "todo: constant arrays not handled yet"
  | Ast.External -> ()

module X86 = struct
  let compile program =
    let lower_isa ~f ~args ~cfg =
      let state = Select_x86.State.init () in
      let args, cfg = Select_x86.codegen_function ~args state cfg in
      Format.printf "===================================\n";
      Format.printf "%s's cfg after codegen:\n" f;
      Format.printf "===================================\n";
      Format.printf "%a\n" X86.Printer.pp_graph cfg;
      let extra = X86.Cfg.precalculate_edges cfg in
      let module Dom = Dominator.Make (X86.Cfg) ((val extra)) in
      let module Loop = Loopnesting.Make (X86.Cfg) (Dom) in
      let module IntRegClass = struct
        (* 16 registers - r10 register - rsp register - (rbp register if frame pointer is enabled) *)
        let k = 16 - 2 - if Option.is_some state.frame_pointer then 1 else 0
        let reg_class = X86.Target.Int
        module Target = X86.Target
      end in
      let module FloatRegClass = struct
        (* 16 registers - xmm10 register *)
        let k = 16 - 1
        let reg_class = X86.Target.Float
        module Target = X86.Target
      end in
      let module X86SpillInt = Spill.X86 (IntRegClass) in
      let module X86SpillFloat = Spill.X86 (FloatRegClass) in
      let int_args = List.filter X86SpillInt.Matches.matches args in
      let float_args = List.filter X86SpillFloat.Matches.matches args in
      let cfg =
        X86SpillInt.spill_helper ~args:int_args (module Loop) state cfg
      in
      let cfg =
        X86SpillFloat.spill_helper ~args:float_args (module Loop) state cfg
      in
      Format.printf "===================================\n";
      Format.printf "%s after spilling:\n" f;
      Format.printf "===================================\n";
      Format.printf "%a\n" X86.Printer.pp_graph cfg;
      let int_regs =
        X86.Regs.int_regs
        |> List.filter_map (fun ((_, _, reg) as r) ->
            if
              Option.equal X86.Target.equal_reg state.frame_pointer
                (Some (Physical r))
            then None
            else if reg <> "r10" && reg <> "rsp" then
              Some (X86.Target.Physical r)
            else None)
        |> Array.of_list
      in
      let float_regs =
        X86.Regs.float_regs
        |> List.filter_map (fun ((_, _, reg) as r) ->
            if reg <> "xmm10" then Some (X86.Target.Physical r) else None)
        |> Array.of_list
      in
      let module Helper = Regalloc.X86Helper (Loop) (IntRegClass) in
      let cfg =
        Helper.regalloc ~args:(X86.Target.RegSet.of_list int_args)
          ~regs:int_regs state cfg (fun _ -> ())
      in
      Format.printf "===================================\n";
      Format.printf "%s after integer register allocation:\n" f;
      Format.printf "===================================\n";
      Format.printf "%a\n" X86.Printer.pp_graph cfg;
      let module Helper = Regalloc.X86Helper (Loop) (FloatRegClass) in
      let cfg =
        Helper.regalloc ~args:(X86.Target.RegSet.of_list float_args)
          ~regs:float_regs state cfg (fun _ -> ())
      in
      Format.printf "===================================\n";
      Format.printf "%s after float register allocation:\n" f;
      Format.printf "===================================\n";
      Format.printf "%a\n" X86.Printer.pp_graph cfg;
      let cfg = X86.SequentializeInt.sequentialize cfg in
      let cfg = X86.SequentializeFloat.sequentialize cfg in
      let cfg = Cleanup_x86.cleanup state X86.Regs.r10 X86.Regs.xmm10 cfg in
      ((state.stack_offset, state.frame_pointer), cfg)
    in
    compile_shared lower_isa program

  let write_file out program =
    let out = Format.formatter_of_out_channel out in
    List.iter (write_global out) program.Ast.globals;
    Format.fprintf out ".global main\n.text\n";
    let write_decl = function
      | Ast.Function (f, _args, _ret, (state, body)) ->
        Format.fprintf out "%s: %a\n" f (X86.Writer.pp_graph state) body
      | Ast.Procedure (f, _args, (state, body)) ->
        Format.fprintf out "%s: %a\n" f (X86.Writer.pp_graph state) body
    in
    List.iter write_decl program.Ast.decls;
    let state, main = program.main in
    Format.fprintf out "main: %a\n" (X86.Writer.pp_graph state) main
end

module Arm = struct
  let compile program =
    let lower_isa ~f ~args ~cfg =
      let state = Select_arm.State.init () in
      let args, cfg = Select_arm.codegen_function ~args state cfg in
      Format.printf "===================================\n";
      Format.printf "%s's cfg after codegen:\n" f;
      Format.printf "===================================\n";
      Format.printf "%a\n" Arm.Cfg.pp_graph cfg;
      let extra = Arm.Cfg.precalculate_edges cfg in
      let module Dom = Dominator.Make (Arm.Cfg) ((val extra)) in
      let module Loop = Loopnesting.Make (Arm.Cfg) (Dom) in
      let module IntRegClass = struct
        (* 31 registers - x10 register - x11 register - (x29 register if frame pointer is enabled) *)
        let k = 31 - 2 - if Option.is_some state.frame_pointer then 1 else 0
        let reg_class = Arm.Target.Int
        module Target = Arm.Target
      end in
      let module FloatRegClass = struct
        (* 32 registers - d20 register - d21 register *)
        let k = 32 - 2
        let reg_class = Arm.Target.Float
        module Target = Arm.Target
      end in
      let module ArmSpillInt = Spill.Arm (IntRegClass) in
      let module ArmSpillFloat = Spill.Arm (FloatRegClass) in
      let int_args = List.filter ArmSpillInt.Matches.matches args in
      let float_args = List.filter ArmSpillFloat.Matches.matches args in
      let cfg =
        ArmSpillInt.spill_helper ~args:int_args (module Loop) state cfg
      in
      let cfg =
        ArmSpillFloat.spill_helper ~args:float_args (module Loop) state cfg
      in
      let int_regs =
        Arm.Regs.int_regs
        |> List.filter_map (fun ((_, _, reg) as r) ->
            if
              Option.equal Arm.Target.equal_reg state.frame_pointer
                (Some (Physical r))
            then None
            else if reg <> "x10" && reg <> "x11" then
              Some (Arm.Target.Physical r)
            else None)
        |> Array.of_list
      in
      let float_regs =
        Arm.Regs.float_regs
        |> List.filter_map (fun ((_, _, reg) as r) ->
            if
              Option.equal Arm.Target.equal_reg state.frame_pointer
                (Some (Physical r))
            then None
            else if reg <> "d20" && reg <> "d21" then
              Some (Arm.Target.Physical r)
            else None)
        |> Array.of_list
      in
      let module Helper = Regalloc.ArmHelper (Loop) (IntRegClass) in
      let cfg =
        Helper.regalloc ~args:(Arm.Target.RegSet.of_list args)
          ~regs:int_regs state cfg (fun _ -> ())
      in
      Format.printf "===================================\n";
      Format.printf "%s after integer register allocation:\n" f;
      Format.printf "===================================\n";
      Format.printf "%a\n" Arm.Printer.pp_graph cfg;
      let module Helper = Regalloc.ArmHelper (Loop) (FloatRegClass) in
      let cfg =
        Helper.regalloc ~args:(Arm.Target.RegSet.of_list float_args)
          ~regs:float_regs state cfg (fun _ -> ())
      in
      Format.printf "===================================\n";
      Format.printf "%s after float register allocation:\n" f;
      Format.printf "===================================\n";
      Format.printf "%a\n" Arm.Printer.pp_graph cfg;
      let cfg = Arm.SequentializeInt.sequentialize cfg in
      let cfg = Arm.SequentializeFloat.sequentialize cfg in
      let cfg = Cleanup_arm.cleanup state Arm.Regs.x10 Arm.Regs.x11 cfg in
      ((state.stack_offset, state.frame_pointer), cfg)
    in
    compile_shared lower_isa program

  let write_file out program =
    let out = Format.formatter_of_out_channel out in
    List.iter (write_global out) program.Ast.globals;
    Format.fprintf out ".global main\n.text\n";
    let write_decl = function
      | Ast.Function (f, _args, _ret, (state, body)) ->
        Format.fprintf out "%s: %a\n" f (Arm.Writer.pp_graph state) body
      | Ast.Procedure (f, _args, (state, body)) ->
        Format.fprintf out "%s: %a\n" f (Arm.Writer.pp_graph state) body
    in
    List.iter write_decl program.decls;
    let state, main = program.main in
    Format.fprintf out "main: %a\n" (Arm.Writer.pp_graph state) main
end
