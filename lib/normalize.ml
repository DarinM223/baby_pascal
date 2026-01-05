module Name = struct
  type t = string * int [@@deriving show, eq, ord]
end

module NameSet = struct
  include CCSet.Make (Name)
  let pp = pp Name.pp
end

module Target = struct
  type label = int * string [@@deriving show, eq]
  type reg = Name.t [@@deriving show, eq]
  type operand =
    | Const of int
    | Reg of reg
    | Label of label
  [@@deriving show, eq]
  type info = {
    uses : NameSet.t;
    defs : NameSet.t;
  }
  [@@deriving show, eq]
  type instr = info * string * operand list [@@deriving show, eq]

  type cond =
    | LT
    | LE
    | GT
    | GE
    | EQ
    | NE

  let cond_of_bop = function
    | Ast.Lt -> LT
    | Ast.Le -> LE
    | Ast.Gt -> GT
    | Ast.Ge -> GE
    | Ast.Eq -> EQ
    | Ast.Neq -> NE
    | _ -> failwith "Invalid binary operator"

  let init_info = { uses = NameSet.empty; defs = NameSet.empty }

  let regset_of_operand = function
    | Const _ | Label _ -> NameSet.empty
    | Reg reg -> NameSet.singleton reg

  let assign ~dest ~src =
    ( { uses = regset_of_operand src; defs = regset_of_operand dest },
      ":=",
      [ dest; src ] )
  let call f es =
    ( {
        init_info with
        uses =
          List.fold_left
            (fun acc o -> NameSet.union acc (regset_of_operand o))
            (NameSet.singleton f) es;
      },
      "call",
      Reg f :: es )
  let goto label = (init_info, "j", [ Label label ])
  let cbranch ~uses (cond : cond) l1 l2 =
    let instr =
      match cond with
      | LT -> "jl"
      | LE -> "jle"
      | GT -> "jg"
      | GE -> "jge"
      | EQ -> "jz"
      | NE -> "jnz"
    in
    ( { init_info with uses = NameSet.of_list uses },
      instr,
      Label l1 :: Label l2 :: List.map (fun r -> Reg r) uses )
  let return ~uses = ({ init_info with uses = NameSet.of_list uses }, "ret", [])
  let uop op ~dest ~src =
    let instr =
      match op with
      | Ast.Not -> "not"
    in
    ( { uses = regset_of_operand src; defs = regset_of_operand dest },
      instr,
      [ dest; src ] )
  let bop (op : Ast.bop) ~dest ~src1 ~src2 =
    let instr =
      match op with
      | Ast.Add -> "add"
      | Ast.Sub -> "sub"
      | Ast.Mul -> "mul"
      | Ast.And -> "and"
      | Ast.Or -> "or"
      | Ast.Eq -> "eq"
      | Ast.Neq -> "neq"
      | Ast.Lt -> "lt"
      | Ast.Le -> "le"
      | Ast.Gt -> "gt"
      | Ast.Ge -> "ge"
    in
    ( {
        uses = NameSet.union (regset_of_operand src1) (regset_of_operand src2);
        defs = regset_of_operand dest;
      },
      instr,
      [ dest; src1; src2 ] )
end

module Cfg = Graph.Make (Target)

let reg s = (s, -1)

let normalize (stmts : Ast.stmt list) : Cfg.graph =
  let ( let* ) = ( @@ ) in
  let new_label : unit -> Cfg.label =
    let c = ref (-1) in
    fun () ->
      incr c;
      let i = !c in
      (i, "label" ^ string_of_int i)
  in
  let fresh : unit -> Target.reg =
    let c = ref (-1) in
    fun () ->
      incr c;
      reg ("tmp" ^ string_of_int !c)
  in
  let rec go_expr exp (k : Target.operand -> Cfg.nodes) : Cfg.nodes =
    match exp with
    | Ast.Int i -> k (Target.Const i)
    | Ast.Bool b -> k (Target.Const (if b then 1 else 0))
    | Ast.Var v -> k (Target.Reg (reg v))
    | Ast.Uop (uop, e) ->
      let* e = go_expr e in
      let tmp = Target.Reg (fresh ()) in
      Fun.compose (Cfg.instruction (Target.uop uop ~src:e ~dest:tmp)) (k tmp)
    | Ast.Bop (bop, e1, e2) ->
      let* e1 = go_expr e1 in
      let* e2 = go_expr e2 in
      let tmp = Target.Reg (fresh ()) in
      Fun.compose
        (Cfg.instruction (Target.bop bop ~src1:e1 ~src2:e2 ~dest:tmp))
        (k tmp)
    | Ast.Call (f, es) -> go_call (reg f) es k
  and short_circuit t f = function
    | Ast.Bool b -> Cfg.branch (if b then t else f)
    | Ast.Uop (Ast.Not, e) -> short_circuit f t e
    | Ast.Bop (Ast.And, e1, e2) ->
      let t' = new_label () in
      fun zgraph ->
        short_circuit t' f e1 @@ Cfg.label t' @@ short_circuit t f e2 @@ zgraph
    | Ast.Bop (Ast.Or, e1, e2) ->
      let f' = new_label () in
      fun zgraph ->
        short_circuit t f' e1 @@ Cfg.label f' @@ short_circuit t f e2 @@ zgraph
    | Ast.Bop (bop, e1, e2) ->
      let* e1 = go_expr e1 in
      let* e2 = go_expr e2 in
      let cond = Target.cond_of_bop bop in
      let uses =
        List.append
          (NameSet.to_list (Target.regset_of_operand e1))
          (NameSet.to_list (Target.regset_of_operand e2))
      in
      Cfg.cbranch uses cond ~ifso:t ~ifnot:f
    | _ -> failwith "Invalid expression for short circuiting"
  and go_call f es k =
    let rec go acc = function
      | e :: es ->
        let* e = go_expr e in
        go (e :: acc) es
      | [] ->
        let es = List.rev acc in
        let tmp = Target.Reg (fresh ()) in
        Fun.compose (Cfg.instruction (Target.call f es)) (k tmp)
    in
    go [] es
  and go_stmt (next : Cfg.label) = function
    | Ast.Assign (v, e) ->
      let* e = go_expr e in
      Cfg.instruction @@ Target.assign ~dest:(Reg (reg v)) ~src:e
    | Ast.If (test, thn, []) ->
      let t = new_label () in
      fun zgraph ->
        short_circuit t next test @@ Cfg.label t
        @@ List.fold_right (go_stmt next) thn
        @@ zgraph
    | Ast.If (test, thn, els) ->
      let t = new_label () in
      let f = new_label () in
      fun zgraph ->
        short_circuit t f test @@ Cfg.label t
        @@ List.fold_right (go_stmt next) thn
        @@ Cfg.branch next @@ Cfg.label f
        @@ List.fold_right (go_stmt next) els
        @@ zgraph
    | Ast.While (test, body) ->
      let begin_label = new_label () in
      let t = new_label () in
      fun zgraph ->
        Cfg.label begin_label @@ short_circuit t next test @@ Cfg.label t
        @@ List.fold_right (go_stmt begin_label) body
        @@ Cfg.branch begin_label @@ zgraph
    | Ast.Call (f, es) -> go_call (reg f) es Fun.(const id)
  in
  Cfg.unfocus
  @@ List.fold_right
       (fun stmt acc ->
         let next = new_label () in
         go_stmt next stmt @@ Cfg.label next @@ acc)
       stmts
       Cfg.(entry empty)
