module Name = struct
  type t = string * int [@@deriving eq, ord]

  let tombstone = ("", -999)
  let is_tombstone n = n == tombstone
  let pp fmt n =
    if is_tombstone n then Format.pp_print_string fmt "tombstone"
    else
      match n with
      | s, -1 -> Format.pp_print_string fmt s
      | s, d -> Format.fprintf fmt "%s_%d" s d
  let label (s, _) = s
  let index (_, i) = i
  let update_index i ((s, _) as n) = if is_tombstone n then n else (s, i)
end

module NameSet = struct
  include CCSet.Make (Name)
  let pp = pp Name.pp
end

module Target = struct
  type label = int * string [@@deriving show, eq]
  type reg = Name.t [@@deriving show, eq]
  type regs = reg list [@@deriving show, eq]
  let pp_regs fmt regs =
    pp_regs fmt @@ List.filter (fun n -> not (Name.is_tombstone n)) regs
  let show_regs regs =
    show_regs @@ List.filter (fun n -> not (Name.is_tombstone n)) regs
  let equal_regs a b =
    equal_regs
      (List.filter (fun n -> not (Name.is_tombstone n)) a)
      (List.filter (fun n -> not (Name.is_tombstone n)) b)

  type operand =
    | Const of int
    | Reg of reg
    | Label of label * operands
  and operands = operand list [@@deriving show, eq]
  let tombstone = Reg Name.tombstone
  let is_tombstone = function
    | Reg r -> Name.is_tombstone r
    | _ -> false
  let pp_operands fmt operands =
    pp_operands fmt @@ List.filter (fun o -> not (is_tombstone o)) operands
  let show_operands operands =
    show_operands @@ List.filter (fun o -> not (is_tombstone o)) operands
  let equal_operands a b =
    equal_operands
      (List.filter (fun o -> not (is_tombstone o)) a)
      (List.filter (fun o -> not (is_tombstone o)) b)

  type cond =
    | LT
    | LE
    | GT
    | GE
    | EQ
    | NE
  [@@deriving show, eq]

  (* destination goes before sources for operands *)
  type instr =
    | Assign of operand * operand
    | Call of operand * operand * operands
    | Goto of label * operands
    | Cbranch of operand * operand * cond * label * operands * label * operands
    | Return of operands
    | Uop of operand * Ast.uop * operand
    | Bop of operand * Ast.bop * operand * operand
  [@@deriving show, eq]

  let cond_of_bop = function
    | Ast.Lt -> LT
    | Ast.Le -> LE
    | Ast.Gt -> GT
    | Ast.Ge -> GE
    | Ast.Eq -> EQ
    | Ast.Neq -> NE
    | _ -> failwith "Invalid binary operator"

  let rec regset_of_operand = function
    | Const _ -> NameSet.empty
    | Label (_, args) ->
      args
      |> List.filter (fun n -> not (is_tombstone n))
      |> List.fold_left
           (fun acc o -> NameSet.union acc (regset_of_operand o))
           NameSet.empty
    | Reg reg ->
      if Name.is_tombstone reg then NameSet.empty else NameSet.singleton reg

  let name (s : string) : Name.t = (s, -1)
  let reg r = Reg (name r)

  let srcs = function
    | Assign (_, o) -> [ o ]
    | Call (_, o1, o2) -> o1 :: o2
    | Goto (l, args) -> [ Label (l, args) ]
    | Cbranch (o1, o2, _, l1, l1args, l2, l2args) ->
      [ Label (l1, l1args); Label (l2, l2args); o1; o2 ]
    | Return o -> o
    | Uop (_, _, o) -> [ o ]
    | Bop (_, _, o1, o2) -> [ o1; o2 ]
  let dests = function
    | Assign (o, _) -> [ o ]
    | Call (o, _, _) -> [ o ]
    | Goto (_, _) -> []
    | Cbranch (_, _, _, _, _, _, _) -> []
    | Return _ -> []
    | Uop (o, _, _) -> [ o ]
    | Bop (o, _, _, _) -> [ o ]

  let uses instr =
    srcs instr |> List.map regset_of_operand
    |> List.fold_left NameSet.union NameSet.empty
  let defs instr =
    dests instr |> List.map regset_of_operand
    |> List.fold_left NameSet.union NameSet.empty
  let map_uses f =
    let f = function
      | Reg reg when Name.is_tombstone reg -> Reg reg
      | operand -> f operand
    in
    function
    | Assign (d, s) -> Assign (d, f s)
    | Call (d, sf, s) ->
      let sf = f sf in
      Call (d, sf, List.map f s)
    | Goto (l, args) -> begin
      match f (Label (l, args)) with
      | Label (l, args) -> Goto (l, args)
      | _ -> failwith "map_uses: goto label transformed into different operand"
    end
    | Cbranch (o1, o2, c, l1, l1args, l2, l2args) ->
      let o1 = f o1 in
      let o2 = f o2 in
      let ol1 = f (Label (l1, l1args)) in
      let ol2 = f (Label (l2, l2args)) in
      begin match (ol1, ol2) with
      | Label (l1, l1args), Label (l2, l2args) ->
        Cbranch (o1, o2, c, l1, l1args, l2, l2args)
      | _ ->
        failwith "map_uses: cbranch label transformed into different operand"
      end
    | Return o -> Return (List.map f o)
    | Uop (d, op, s) -> Uop (d, op, f s)
    | Bop (d, op, s1, s2) ->
      let s1 = f s1 in
      Bop (d, op, s1, f s2)
  let map_defs f =
    let f = function
      | Reg reg when Name.is_tombstone reg -> Reg reg
      | operand -> f operand
    in
    function
    | Assign (d, s) -> Assign (f d, s)
    | Call (d, sf, s) -> Call (f d, sf, s)
    | Goto (l, args) -> Goto (l, args)
    | Cbranch (o1, o2, c, l1, l1args, l2, l2args) ->
      Cbranch (o1, o2, c, l1, l1args, l2, l2args)
    | Return o -> Return o
    | Uop (d, op, s) -> Uop (f d, op, s)
    | Bop (d, op, s1, s2) -> Bop (f d, op, s1, s2)

  let assign ~dest ~src = Assign (dest, src)
  let call ~dest f es = Call (dest, f, es)
  let goto label args = Goto (label, args)
  let cbranch ~args (cond : cond) l1 l1args l2 l2args =
    match args with
    | [ o1; o2 ] -> Cbranch (o1, o2, cond, l1, l1args, l2, l2args)
    | _ -> failwith "cbranch expects only two arguments currently"
  let return ~uses = Return (List.map (fun r -> Reg r) uses)
  let uop op ~dest ~src = Uop (dest, op, src)
  let bop (op : Ast.bop) ~dest ~src1 ~src2 = Bop (dest, op, src1, src2)
end

module Cfg = Graph.Make (Target)
module Flow = Dataflow.Make (Cfg)

let normalize (stmts : Ast.stmt list) : Cfg.graph =
  let ( let* ) = ( @@ ) in
  let new_label : unit -> Cfg.label =
    let c = ref 0 in
    fun () ->
      incr c;
      let i = !c in
      (i, "label" ^ string_of_int i)
  in
  let fresh : unit -> Target.reg =
    let c = ref (-1) in
    fun () ->
      incr c;
      Target.name ("tmp" ^ string_of_int !c)
  in
  let rec go_expr exp (k : Target.operand -> Cfg.nodes) : Cfg.nodes =
    match exp with
    | Ast.Int i -> k (Target.Const i)
    | Ast.Bool b -> k (Target.Const (if b then 1 else 0))
    | Ast.Var v -> k (Target.reg v)
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
    | Ast.Call (f, es) -> go_call (Target.reg f) es k
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
      Cfg.cbranch ~args:[ e1; e2 ] cond ~ifso:t ~ifnot:f
    | _ -> failwith "Invalid expression for short circuiting"
  and go_call f es k =
    let rec go acc = function
      | e :: es ->
        let* e = go_expr e in
        go (e :: acc) es
      | [] ->
        let es = List.rev acc in
        let tmp = Target.Reg (fresh ()) in
        Fun.compose (Cfg.instruction (Target.call ~dest:tmp f es)) (k tmp)
    in
    go [] es
  and go_stmt (next : Cfg.label) = function
    | Ast.Assign (v, e) ->
      let* e = go_expr e in
      Cfg.instruction @@ Target.assign ~dest:(Target.reg v) ~src:e
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
    | Ast.Call (f, es) -> go_call (Target.reg f) es Fun.(const id)
  in
  Cfg.unfocus
  @@ List.fold_right
       (fun stmt acc ->
         let next = new_label () in
         go_stmt next stmt @@ Cfg.label next @@ acc)
       stmts
       Cfg.(focus_entry empty)
