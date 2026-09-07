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

  let flipped f = fun (op, a, b) -> f (op, b, a)

  let rec simplify_binop_instruction max_recurse =
    let open Undag.Target in
    function
    | Ast.Add, Const i, Const j -> Some (Const (i + j))
    | Ast.Add, Const i, op2 ->
      simplify_binop_instruction max_recurse (Ast.Add, op2, Const i)
    | Ast.Add, op1, Const 0 -> Some op1
    | Ast.Add, op1, Instr (Bop (_, Ast.Sub, op2, op1'))
      when Undag.Target.equal_operand op1 op1' ->
      Some op2
    | Ast.Add, Instr (Bop (_, Ast.Sub, op2, op1)), op1'
      when Undag.Target.equal_operand op1 op1' ->
      Some op2
    | Ast.Add, op1, op2 -> simplify_associative max_recurse (Ast.Add, op1, op2)
    | Ast.Mul, Const i, Const j -> Some (Const (i * j))
    | Ast.Mul, Const i, op2 ->
      simplify_binop_instruction max_recurse (Ast.Mul, op2, Const i)
    | Ast.Mul, _, Const 0 -> Some (Const 0)
    | Ast.Mul, op1, Const 1 -> Some op1
    | (Ast.Mul, _, _) as instr ->
      instr
      |> try'
           [
             simplify_associative max_recurse;
             simplify_commutative max_recurse Ast.Add;
           ]
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
    | Ast.And, Const i, op2 ->
      simplify_binop_instruction max_recurse (Ast.And, op2, Const i)
    | Ast.And, op1, op2 when Undag.Target.equal_operand op1 op2 -> Some op1
    | Ast.And, _, Const 0 -> Some (Const 0)
    | Ast.And, op1, Const -1 -> Some op1
    | (Ast.And, _, _) as instr ->
      instr
      |> try'
           [
             simplify_and_commutative;
             flipped simplify_and_commutative;
             simplify_associative max_recurse;
             simplify_commutative max_recurse Ast.Or;
           ]
    | Ast.Or, _, Const -1 -> Some (Const (-1))
    | Ast.Or, op1, Const 0 -> Some op1
    | Ast.Or, op1, op2 when Undag.Target.equal_operand op1 op2 -> Some op1
    | (Ast.Or, _, _) as instr ->
      instr
      |> try'
           [
             simplify_or_logic;
             flipped simplify_or_logic;
             simplify_associative max_recurse;
             simplify_commutative max_recurse Ast.And;
           ]
    | _ -> None

  and simplify_and_commutative = function
    | Ast.And, Instr (Uop (_, Ast.Not, op1)), op2
      when Undag.Target.equal_operand op1 op2 ->
      Some (Const 0)
    | Ast.And, Instr (Bop (_, Ast.Or, op1, _)), op2
      when Undag.Target.equal_operand op1 op2 ->
      Some op2
    | ( Ast.And,
        Instr (Bop (_, Ast.Or, x, Instr (Uop (_, Ast.Not, y)))),
        Instr (Bop (_, Ast.Or, x', y')) )
      when Undag.Target.equal_operands [ x; y ] [ x'; y' ] ->
      Some x
    | _ -> None

  and simplify_or_logic = function
    | Ast.Or, x, Instr (Uop (_, Ast.Not, x'))
      when Undag.Target.equal_operand x x' ->
      Some (Const (-1))
    | Ast.Or, x, Instr (Uop (_, Ast.Not, Instr (Bop (_, Ast.And, x', _))))
      when Undag.Target.equal_operand x x' ->
      Some (Const (-1))
    | Ast.Or, x, Instr (Bop (_, Ast.And, x', _))
      when Undag.Target.equal_operand x x' ->
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

  and simplify_commutative max_recurse opex =
    let max_recurse = max_recurse - 1 in
    if max_recurse <= 0 then Fun.const None
    else
      try'
        [
          expand_binop_instruction max_recurse opex;
          flipped (expand_binop_instruction max_recurse opex);
        ]

  and expand_binop_instruction max_recurse opex = function
    | op, (Instr (Bop (_, opex', a, b)) as lhs), c when Ast.equal_bop opex opex'
      ->
      let* l = simplify_binop_instruction max_recurse (op, a, c) in
      let* r = simplify_binop_instruction max_recurse (op, b, c) in
      if
        (Undag.Target.equal_operand l a && Undag.Target.equal_operand r b)
        || is_commutative opex
           && Undag.Target.equal_operand l b
           && Undag.Target.equal_operand r a
      then Some lhs
      else simplify_binop_instruction max_recurse (opex, l, r)
    | _ -> None
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
