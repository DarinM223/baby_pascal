module Converter =
  Instruction.Convert (Undag.Target.Operand) (Normalize.Target.Operand)
module Convert = Converter.Make (Undag.Target) (Normalize.Target)

(* TODO: Value numbering for each instruction:
   1. Call Undag.treeify_instruction with the current mapping to get instruction tree
   2. Call simplify_instruction
   3. Store result in mapping
   4. Run convert_instruction
   5. Add instruction to graph *)

let simplify_instruction =
  let open Undag.Target in
  function
  | Bop (result, Ast.Add, op1, Const 0) -> Assign (result, op1)
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
