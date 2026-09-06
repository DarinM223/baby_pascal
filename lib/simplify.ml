module Converter =
  Instruction.Convert (Undag.Target.Operand) (Normalize.Target.Operand)
module Convert = Converter.Make (Undag.Target) (Normalize.Target)

let rec remove_assigns = function
  | Undag.Target.Instr (Undag.Target.Assign (_, op)) -> remove_assigns op
  | op -> op

let remove_use_assigns = Undag.Target.map_uses remove_assigns

open struct
  open Undag.Target

  let max_recursion_limit = 100
  let try' =
    List.fold_left
      (fun acc f a ->
        match f a with
        | Some v -> Some v
        | None -> acc a)
      (Fun.const None)
  let ( let* ) = Option.bind

  let is_commutative = function
    | Ast.Add | Ast.Mul | Ast.And -> true
    | _ -> false

  let rec simplify_binop_instruction _max_recurse =
    let open Undag.Target in
    function
    | Ast.Add, Const i, Const j -> Some (Const (i + j))
    | Ast.Add, op1, Const 0 -> Some op1
    | Ast.Add, op1, Instr (Bop (_, Ast.Sub, op2, op1'))
      when Undag.Target.equal_operand op1 op1' ->
      Some op2
    | Ast.Add, Instr (Bop (_, Ast.Sub, op2, op1)), op1'
      when Undag.Target.equal_operand op1 op1' ->
      Some op2
    | Ast.Mul, Const i, Const j -> Some (Const (i * j))
    | Ast.Mul, _, Const 0 -> Some (Const 0)
    | Ast.Mul, op1, Const 1 -> Some op1
    | Ast.Div, Const i, Const j -> Some (Const (i / j))
    | Ast.Div, Const 0, _ -> Some (Const 0)
    | Ast.Div, op1, op2 when Undag.Target.equal_operand op1 op2 ->
      Some (Const 1)
    | Ast.Div, op1, Const 1 -> Some op1
    (* todo: check for overflow *)
    | Ast.Div, Instr (Bop (_, Ast.Mul, op1, op2)), op2'
      when Undag.Target.equal_operand op2 op2' ->
      Some op1
    | Ast.And, Const i, Const j -> Some (Const (i land j))
    | Ast.And, op1, op2 when Undag.Target.equal_operand op1 op2 -> Some op1
    | Ast.And, _, Const 0 -> Some (Const 0)
    | Ast.And, op1, Const -1 -> Some op1
    | _ -> None

  and simplify_and_commutative = function
    | Instr (Uop (_, Ast.Not, op1)), op2 when Undag.Target.equal_operand op1 op2
      ->
      Some (Const 0)
    | Instr (Bop (_, Ast.Or, op1, _)), op2
      when Undag.Target.equal_operand op1 op2 ->
      Some op2
    | ( Instr (Bop (_, Ast.Or, x, Instr (Uop (_, Ast.Not, y)))),
        Instr (Bop (_, Ast.Or, x', y')) )
      when Undag.Target.equal_operands [ x; y ] [ x'; y' ] ->
      Some x
    | _ -> None

  and simplify_associative max_recurse =
    let max_recurse = max_recurse - 1 in
    if max_recurse <= 0 then Fun.const None
    else
      try'
        [
          begin function
            | op, (Instr (Bop (_, op', a, b)) as lhs), rhs
              when Ast.equal_bop op op' ->
              let* v = simplify_binop_instruction max_recurse (op, b, rhs) in
              if Undag.Target.equal_operand v b then Some lhs
              else simplify_binop_instruction max_recurse (op, a, v)
            | _ -> None
          end;
          begin function
            | op, lhs, (Instr (Bop (_, op', b, c)) as rhs)
              when Ast.equal_bop op op' ->
              let* v = simplify_binop_instruction max_recurse (op, lhs, b) in
              if Undag.Target.equal_operand v b then Some rhs
              else simplify_binop_instruction max_recurse (op, v, c)
            | _ -> None
          end;
          begin function
            | op, (Instr (Bop (_, op', a, b)) as lhs), rhs
              when is_commutative op && Ast.equal_bop op op' ->
              let* v = simplify_binop_instruction max_recurse (op, rhs, a) in
              if Undag.Target.equal_operand v a then Some lhs
              else simplify_binop_instruction max_recurse (op, v, b)
            | _ -> None
          end;
          begin function
            | op, lhs, (Instr (Bop (_, op', b, c)) as rhs)
              when is_commutative op && Ast.equal_bop op op' ->
              let* v = simplify_binop_instruction max_recurse (op, c, lhs) in
              if Undag.Target.equal_operand v b then Some rhs
              else simplify_binop_instruction max_recurse (op, b, v)
            | _ -> None
          end;
        ]
end

let simplify_instruction = function
  | Undag.Target.Bop (result, op, a, b) as instr ->
    begin match simplify_binop_instruction max_recursion_limit (op, a, b) with
    | Some v -> Undag.Target.Assign (result, v)
    | None -> instr
    end
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
