module Converter =
  Instruction.Convert (Undag.Target.Operand) (Normalize.Target.Operand)
module Convert = Converter.Make (Undag.Target) (Normalize.Target)

let rec remove_assigns = function
  | Undag.Target.Instr (Undag.Target.Assign (_, op)) -> remove_assigns op
  | op -> op

let remove_use_assigns = Undag.Target.map_uses remove_assigns

let simplify_instruction =
  let open Undag.Target in
  function
  | Bop (result, Ast.Add, op1, Const 0) -> Assign (result, op1)
  | Bop (result, Ast.Add, op1, Instr (Bop (_, Ast.Sub, op2, op1')))
    when Undag.Target.equal_operand op1 op1' ->
    Assign (result, op2)
  | instr -> instr

let convert_instruction (instr : Undag.Cfg.Target.instr) :
    Normalize.Target.instr =
  let rec convert_operand (op : Undag.Target.operand) =
    match op with
    | Undag.Target.Const c -> Normalize.Target.Const c
    | Instr i ->
      begin match Undag.Target.dests i with
      | [ dest ] -> convert_operand dest
      | _ ->
        failwith
        @@ Format.asprintf
             "convert_instruction: unknown destination list for instruction %a"
             Undag.Target.pp_instr i
      end
    | Reg reg -> Normalize.Target.Reg reg
    | Label (l, args) ->
      Normalize.Target.Label (l, List.map convert_operand args)
  in
  Convert.convert convert_operand instr
