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

module NameHashtbl = CCHashtbl.Make (struct
  include Name
  let equal = equal
  let hash = Hashtbl.hash
end)

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

  (* TODO: add types to operands *)
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
    let of_operand = function
      | Reg r -> Some r
      | _ -> None
    let to_operand r = Reg r
  end
  module RegSet = NameSet

  let rec regset_of_operand = function
    | Const _ -> RegSet.empty
    | Label (_, args) ->
      args
      |> List.filter (fun n -> not (is_tombstone n))
      |> List.fold_left
           (fun acc o -> RegSet.union acc (regset_of_operand o))
           RegSet.empty
    | Reg reg ->
      if Reg.is_tombstone reg then RegSet.empty else RegSet.singleton reg

  let name (s : string) : Name.t = (s, -1)
  let reg r = Reg (name r)

  let uses instr =
    srcs instr |> List.map regset_of_operand
    |> List.fold_left RegSet.union RegSet.empty
  let defs instr =
    dests instr |> List.map regset_of_operand
    |> List.fold_left RegSet.union RegSet.empty

  let is_side_effectful = function
    | Call _ | Return _ | Alloca _ | Load _ | Store _ -> true
    | _ -> false
end

module Cfg = Graph.Make (Target)
module Flow = Dataflow.Make (Cfg)
module type Fresh = sig
  val fresh : unit -> Target.reg
  val new_label : unit -> Cfg.label
  val reset_names : unit -> unit
  val reset_labels : unit -> unit
end
module Fresh () : Fresh = struct
  let c = ref (-1)
  let fresh () =
    incr c;
    Target.name ("tmp" ^ string_of_int !c)

  let l = ref 0
  let new_label () =
    incr l;
    let i = !l in
    (i, "label" ^ string_of_int i)

  let reset_names () = c := -1
  let reset_labels () = l := 0
end

let normalize (module Fresh : Fresh) (stmt : Ast.stmt) : Cfg.graph =
  let open Fresh in
  let ( let* ) = ( @@ ) in
  let label l =
    if Lazy.is_val l then Cfg.label (Lazy.force l) else fun a -> a
  in
  let rec go_expr exp (k : Target.operand -> Cfg.nodes) : Cfg.nodes =
    match exp with
    | Ast.Int i -> k (Target.Const i)
    | Ast.Bool b -> k (Target.Const (if b then 1 else 0))
    | Ast.Var v -> k (Target.reg v)
    | Ast.Uop (uop, e) ->
      let* e = go_expr e in
      let tmp = Target.Reg (fresh ()) in
      let rest = k tmp in
      fun zgraph ->
        Cfg.instruction (Target.uop uop ~src:e ~dest:tmp) @@ rest @@ zgraph
    | Ast.Bop (bop, e1, e2) ->
      let* e1 = go_expr e1 in
      let* e2 = go_expr e2 in
      let tmp = Target.Reg (fresh ()) in
      let rest = k tmp in
      fun zgraph ->
        Cfg.instruction (Target.bop bop ~src1:e1 ~src2:e2 ~dest:tmp)
        @@ rest @@ zgraph
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
        let rest = k tmp in
        fun zgraph ->
          Cfg.instruction (Target.call ~dest:tmp f es) @@ rest @@ zgraph
    in
    go [] es
  and go_stmt (next : Cfg.label Lazy.t) = function
    | Ast.Assign (v, e) ->
      let* e = go_expr e in
      Cfg.instruction @@ Target.assign ~dest:(Target.reg v) ~src:e
    | Ast.Group stmts ->
      let len = List.length stmts in
      let stmts =
        List.mapi
          (fun i stmt ->
            if i = len - 1 then go_stmt next stmt
            else
              let next = lazy (new_label ()) in
              let stmt = go_stmt next stmt in
              fun zgraph -> stmt @@ label next @@ zgraph)
          stmts
      in
      List.fold_right ( @@ ) stmts
    | Ast.If (test, thn, Group []) ->
      let t = new_label () in
      let branch_cond = short_circuit t (Lazy.force next) test in
      let thn = go_stmt next thn in
      fun zgraph -> branch_cond @@ Cfg.label t @@ thn @@ zgraph
    | Ast.If (test, thn, els) ->
      let t = new_label () in
      let f = new_label () in
      let branch_cond = short_circuit t f test in
      let thn = go_stmt next thn in
      let els = go_stmt next els in
      let jump = Cfg.branch (Lazy.force next) in
      fun zgraph ->
        branch_cond @@ Cfg.label t @@ thn @@ jump @@ Cfg.label f @@ els
        @@ zgraph
    | Ast.While (test, body) ->
      let begin_label = new_label () in
      let t = new_label () in
      let branch_cond = short_circuit t (Lazy.force next) test in
      let body = go_stmt (lazy begin_label) body in
      fun zgraph ->
        Cfg.label begin_label @@ branch_cond @@ Cfg.label t @@ body
        @@ Cfg.branch begin_label @@ zgraph
    | Ast.Call (f, es) -> go_call (Target.Label ((-1, f), [])) es Fun.(const id)
  in
  let next = lazy (new_label ()) in
  let stmt = go_stmt next stmt in
  Cfg.unfocus (stmt @@ label next @@ Cfg.focus_entry Cfg.empty)

let set_return fn_name (graph : Cfg.graph) : Cfg.graph =
  let zblock, rest = Cfg.focus_exit graph in
  match zblock with
  | head, Last Exit ->
    Cfg.unfocus
      ((head, Last (Return (Target.return ~uses:[ Target.reg fn_name ]))), rest)
  | _ -> graph
