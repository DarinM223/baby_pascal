module Name = struct
  type t = string * int [@@deriving show, eq, ord]
end

module NameSet = struct
  include Set.Make (Name)

  let pp fmt s =
    Format.fprintf fmt "S.of_list %s" ([%show: Name.t list] (elements s))
end

module Target = struct
  type label = int * string [@@deriving show]
  type reg = Name.t [@@deriving show]
  type operand =
    | Const of int
    | Reg of reg
    | Label of label
  [@@deriving show]
  type info = {
    uses : NameSet.t;
    defs : NameSet.t;
  }
  [@@deriving show]
  type instr = info * string * operand list [@@deriving show]

  type cond =
    | LT
    | LE
    | GT
    | GE
    | EQ
    | NE

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
    | Ast.Bop (_, _, _) -> failwith ""
    | Ast.Call (f, es) -> go_call (reg f) es k
  and short_circuit _t _f = failwith ""
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
