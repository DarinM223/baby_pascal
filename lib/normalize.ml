module StringSet = struct
  include Set.Make (String)

  let pp fmt s =
    Format.fprintf fmt "S.of_list %s" ([%show: string list] (elements s))
end

module Target = struct
  type label = int * string [@@deriving show]
  type reg = string [@@deriving show]
  type operand =
    | Const of int
    | Reg of reg
    | Label of label
  [@@deriving show]
  type info = {
    uses : StringSet.t;
    defs : StringSet.t;
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

  let init_info = { uses = StringSet.empty; defs = StringSet.empty }

  let regset_of_operand = function
    | Const _ | Label _ -> StringSet.empty
    | Reg reg -> StringSet.singleton reg

  let assign ~dest ~src =
    ( { uses = regset_of_operand src; defs = regset_of_operand dest },
      ":=",
      [ dest; src ] )
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
    ( { init_info with uses = StringSet.of_list uses },
      instr,
      Label l1 :: Label l2 :: List.map (fun r -> Reg r) uses )
  let return ~uses:_ = (init_info, "ret", [])
end

module Cfg = Graph.Make (Target)

let normalize (stmts : Ast.stmt list) : Cfg.graph =
  let ( let* ) = ( @@ ) in
  let new_label : unit -> Cfg.label =
    let c = ref (-1) in
    fun () ->
      incr c;
      let i = !c in
      (i, "label" ^ string_of_int i)
  in
  let rec go_expr exp (k : Target.operand -> Cfg.nodes) : Cfg.nodes =
    match exp with
    | Ast.Int i -> k (Target.Const i)
    | Ast.Bool _ -> failwith ""
    | Ast.Var _ -> failwith ""
    | Ast.Uop (_, _) -> failwith ""
    | Ast.Bop (_, _, _) -> failwith ""
    | Ast.Call (_, _) -> failwith ""
  and short_circuit _t _f = failwith ""
  and go_stmt (next : Cfg.label) = function
    | Ast.Assign (v, e) ->
      let* e = go_expr e in
      Cfg.instruction @@ Target.assign ~dest:(Reg v) ~src:e
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
    | Ast.Call (_f, _es) -> failwith ""
  in
  Cfg.unfocus
  @@ List.fold_right
       (fun stmt acc ->
         let next = new_label () in
         go_stmt next stmt @@ Cfg.label next @@ acc)
       stmts
       Cfg.(entry empty)
