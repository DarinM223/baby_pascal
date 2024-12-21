type op =
  | Neg
  | Not
  | Add
  | Sub
  | Mul
  | Div
  | And
  | Or
  | Goto
  | Lt
  | Le
  | Gt
  | Ge
  | Eq
  | Ne
  | Param
  | Call
  | Assign
  | Load
  | Nop
[@@deriving show, eq]

module Addr = struct
  type t =
    | Const of int
    | Name of int * int
    | Temp of int
    | Empty
  [@@deriving show, eq, ord]
end

let name sym = Addr.Name (sym, -1)

type quad = {
  mutable op : op;
  mutable a : Addr.t;
  mutable b : Addr.t;
  mutable r : Addr.t;
}
[@@deriving show, eq]

let push_quad v (op, a, b, r) = CCVector.push v { op; a; b; r }
let op_of_uop = function
  | Ast.Not -> Not

let op_of_bop = function
  | Ast.Add -> Add
  | Ast.Sub -> Sub
  | Ast.Mul -> Mul
  | Ast.And -> And
  | Ast.Or -> Or
  | Ast.Eq -> Eq
  | Ast.Neq -> Ne
  | Ast.Lt -> Lt
  | Ast.Le -> Le
  | Ast.Gt -> Gt
  | Ast.Ge -> Ge

module Make (Fresh : Intf.Fresh) (Sym : Intf.Sym) = struct
  let normalize stmts =
    let len = List.length stmts in
    let code =
      CCVector.create_with ~capacity:len
        { op = Nop; a = Empty; b = Empty; r = Empty }
    in
    let label_table = Hashtbl.create 100 in
    let new_label =
      let i = ref (-1) in
      fun () ->
        incr i;
        !i
    in
    let label l = Hashtbl.add label_table l (CCVector.length code) in
    let rec addr_of_expr = function
      | Ast.Int i -> Addr.Const i
      | Ast.Bool b -> if b then Const 1 else Const 0
      | Ast.Var v -> name (Sym.get_sym v)
      | Ast.Uop (uop, e) ->
        let addr = addr_of_expr e in
        let tmp = Addr.Temp (Fresh.fresh ()) in
        push_quad code (op_of_uop uop, addr, Empty, tmp);
        tmp
      | Ast.Bop (bop, e1, e2) ->
        let addr1 = addr_of_expr e1 in
        let addr2 = addr_of_expr e2 in
        let tmp = Addr.Temp (Fresh.fresh ()) in
        push_quad code (op_of_bop bop, addr1, addr2, tmp);
        tmp
      | Ast.Call (f, es) -> go_call f es (Addr.Temp (Fresh.fresh ()))
    and go_call f es tmp =
      let addrs = List.map addr_of_expr es in
      List.iter (fun addr -> push_quad code (Param, addr, Empty, Empty)) addrs;
      push_quad code (Call, name (Sym.get_sym f), Const (List.length es), tmp);
      tmp
    and short_circuit t f = function
      | Ast.Uop (Ast.Not, e) -> short_circuit f t e
      | Ast.Bool b ->
        push_quad code (Goto, Const (if b then t else f), Empty, Empty)
      | Ast.Bop (Ast.And, e1, e2) ->
        let t' = new_label () in
        short_circuit t' f e1;
        label t';
        short_circuit t f e2
      | Ast.Bop (Ast.Or, e1, e2) ->
        let f' = new_label () in
        short_circuit t f' e1;
        label f';
        short_circuit t f e2
      | Ast.Bop (rel, e1, e2) ->
        let addr1 = addr_of_expr e1 in
        let addr2 = addr_of_expr e2 in
        push_quad code (op_of_bop rel, addr1, addr2, Const t);
        push_quad code (Goto, Const f, Empty, Empty)
      | _ -> failwith "Invalid expression for short circuiting bool operation"
    and go_stmt next = function
      | Ast.Assign (v, e) ->
        let addr = addr_of_expr e in
        let s = Sym.get_sym v in
        push_quad code (Assign, addr, Empty, name s)
      | Ast.If (test, thn, []) ->
        let t = new_label () in
        short_circuit t next test;
        label t;
        List.iter (go_stmt next) thn
      | Ast.If (test, thn, els) ->
        let t = new_label () in
        let f = new_label () in
        short_circuit t f test;
        label t;
        List.iter (go_stmt next) thn;
        push_quad code (Goto, Const next, Empty, Empty);
        label f;
        List.iter (go_stmt next) els
      | Ast.While (test, body) ->
        let begin_label = new_label () in
        let t = new_label () in
        label begin_label;
        short_circuit t next test;
        label t;
        List.iter (go_stmt begin_label) body;
        push_quad code (Goto, Const begin_label, Empty, Empty)
      | Ast.Call (f, es) -> ignore (go_call f es Empty)
    in
    List.iter
      (fun stmt ->
        let next = new_label () in
        go_stmt next stmt;
        label next)
      stmts;
    (* Rewrite labels in quad operands to the actual index in the code where the label starts *)
    let rewrite_labels_in_quad = function
      | { op = Goto; a = Const l; _ } as quad ->
        quad.a <- Const (Hashtbl.find label_table l)
      | { op = Eq | Ne | Gt | Ge | Lt | Le; r = Const l; _ } as quad ->
        quad.r <- Const (Hashtbl.find label_table l)
      | _ -> ()
    in
    CCVector.iter rewrite_labels_in_quad code;
    push_quad code (Nop, Empty, Empty, Empty);
    code
end
