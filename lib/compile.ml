let compile program =
  Check.check_program program;
  let module F = Normalize.Fresh () in
  let program =
    let open Ast in
    let normalize_decl = function
      | Function (f, ps, t, body) ->
        Function (f, ps, t, Normalize.(set_return f (normalize (module F) body)))
      | Procedure (f, ps, body) ->
        Procedure (f, ps, Normalize.normalize (module F) body)
    in
    {
      program with
      main = Normalize.normalize (module F) program.main;
      decls = List.map normalize_decl program.decls;
    }
  in
  let rec round args cfg =
    let cfg, changed = Deadcode.M.deadcode cfg in
    let cfg, changed' =
      let block_args = Constprop.block_args cfg in
      Constprop.constprop block_args args cfg
    in
    if changed || changed' then round args cfg else cfg
  in
  let lower_cfg f args cfg =
    let extra = Normalize.Cfg.precalculate_edges cfg in
    let module Extra = (val extra) in
    let module Dom = Dominator.Make (Normalize.Cfg) (Extra) in
    let a_orig = Construct.calc_a_orig cfg in
    let live = Construct.calc_live cfg in
    let cfg = Construct.insert_phis_pruned live (module Dom) a_orig cfg in
    let cfg = Construct.rename_variables (module Dom) cfg in
    let args = List.map (fun arg -> (arg, 0)) args in
    Format.printf "===================================\n";
    Format.printf "%s's initial cfg:\n" f;
    Format.printf "===================================\n";
    Format.printf "%a\n" Normalize.Cfg.pp_graph cfg;
    let cfg = round args cfg in
    Format.printf "===================================\n";
    Format.printf "%s's cfg after optimization passes:\n" f;
    Format.printf "===================================\n";
    Format.printf "%a\n" Normalize.Cfg.pp_graph cfg;
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
    Format.printf "%a\n" Normalize.Cfg.pp_graph cfg;
    let cfg =
      Normalize.Cfg.Blocks.fold
        (fun _ block acc -> Undag.Cfg.Blocks.insert (Undag.undag block) acc)
        cfg Undag.Cfg.empty
    in
    let state = Select_x86.State.init () in
    let args, cfg = Select_x86.codegen_function ~args state cfg in
    Format.printf "===================================\n";
    Format.printf "%s's cfg after codegen:\n" f;
    Format.printf "===================================\n";
    Format.printf "%a\n" X86.Cfg.pp_graph cfg;
    let extra = X86.Cfg.precalculate_edges cfg in
    let module Dom = Dominator.Make (X86.Cfg) ((val extra)) in
    let module Loop = Loopnesting.Make (X86.Cfg) (Dom) in
    let cfg = Spill.X86.spill_helper ~args (module Loop) state cfg in
    let regs =
      X86.Regs.int_regs
      |> List.filter_map (fun ((_, _, reg) as r) ->
          if reg <> "r10" && reg <> "rsp" then Some (X86.Target.Physical r)
          else None)
      |> Array.of_list
    in
    let module Helper = Regalloc.X86Helper (Loop) in
    let cfg =
      Helper.regalloc ~args:(X86.Target.RegSet.of_list args) ~regs state cfg
        (fun _ -> ())
    in
    Format.printf "===================================\n";
    Format.printf "%s after register allocation:\n" f;
    Format.printf "===================================\n";
    Format.printf "%a\n" X86.Printer.pp_graph cfg;
    let cfg = X86.Sequentialize.sequentialize cfg in
    let cfg = Cleanup_x86.cleanup state X86.Regs.r10 cfg in
    ((state.stack_offset, state.frame_pointer), cfg)
  in
  let lower_decl = function
    | Ast.Function (f, args, ret, body) ->
      Ast.Function (f, args, ret, lower_cfg f (List.map fst args) body)
    | Ast.Procedure (f, args, body) ->
      Ast.Procedure (f, args, lower_cfg f (List.map fst args) body)
  in
  let decls = List.map lower_decl program.decls in
  let main = lower_cfg "main" [] program.main in
  { program with decls; main }

let write_file out program =
  let out = Format.formatter_of_out_channel out in
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
