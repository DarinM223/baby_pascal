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

  module Operand = struct
    type label = int * string [@@deriving show, eq]
    type 'a t =
      | Const of int
      | Reg of reg
      | Label of label * 'a ts
    and 'a ts = 'a t list [@@deriving show, eq]
    let label l ops = Label (l, ops)
    let destruct_label = function
      | Label (l, ops) -> Some (l, ops)
      | _ -> None
    let tombstone = Reg Name.tombstone
    let is_tombstone = function
      | Reg r -> Name.is_tombstone r
      | _ -> false
    let pp_ts f fmt operands =
      pp_ts f fmt @@ List.filter (fun o -> not (is_tombstone o)) operands
    let show_ts f operands =
      show_ts f @@ List.filter (fun o -> not (is_tombstone o)) operands
    let equal_ts f a b =
      equal_ts f
        (List.filter (fun o -> not (is_tombstone o)) a)
        (List.filter (fun o -> not (is_tombstone o)) b)
    type 'a operand = 'a t [@@deriving show, eq]
    type 'a operands = 'a ts [@@deriving show, eq]
  end
  include Operand
  include Instruction.Make (Operand)
  module Reg = struct
    include Name
    let to_operand r = Reg r
  end
  module RegSet = NameSet

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

  let uses instr =
    srcs instr |> List.map regset_of_operand
    |> List.fold_left NameSet.union NameSet.empty
  let defs instr =
    dests instr |> List.map regset_of_operand
    |> List.fold_left NameSet.union NameSet.empty
end

module Cfg = Graph.Make (Target)
module Flow = Dataflow.Make (Cfg)
module Fresh () = struct
  let c = ref (-1)
  let fresh () =
    incr c;
    Target.name ("tmp" ^ string_of_int !c)
  let reset () = c := -1
end

let normalize (fresh : unit -> Target.reg) (stmts : Ast.stmt list) : Cfg.graph =
  let ( let* ) = ( @@ ) in
  let new_label : unit -> Cfg.label =
    let c = ref 0 in
    fun () ->
      incr c;
      let i = !c in
      (i, "label" ^ string_of_int i)
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
    | Ast.Call (f, es) -> go_call (Target.Label ((-1, f), [])) es k
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
    | Ast.Call (f, es) -> go_call (Target.Label ((-1, f), [])) es Fun.(const id)
  in
  Cfg.unfocus
  @@ List.fold_right
       (fun stmt acc ->
         let next = new_label () in
         go_stmt next stmt @@ Cfg.label next @@ acc)
       stmts
       Cfg.(focus_entry empty)

let set_return fn_name (graph : Cfg.graph) : Cfg.graph =
  let zblock, rest = Cfg.focus_exit graph in
  match zblock with
  | head, Last Exit ->
    Cfg.unfocus
      ((head, Last (Return (Target.return ~uses:[ Target.reg fn_name ]))), rest)
  | _ -> graph
