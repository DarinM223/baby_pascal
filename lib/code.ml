open Utils

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
  | Return
  | Nop
[@@deriving show, eq]

type addr = Const of int | Name of int | Temp of int | Empty
[@@deriving show, eq]

type quad = op * addr * addr * addr [@@deriving show, eq]

let op_of_uop = function Ast.Not -> Not

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

module Make (Fresh : Fresh) (Sym : Sym) = struct
  open Fresh
  open Sym

  let normalize stmts =
    let len = List.length stmts in
    let code = CCVector.create_with ~capacity:len (Nop, Empty, Empty, Empty) in
    let label_table = Hashtbl.create 100 in
    let new_label =
      let i = ref (-1) in
      fun () ->
        incr i;
        !i
    in
    let label l = Hashtbl.add label_table l (CCVector.length code) in
    let rec addr_of_expr = function
      | Ast.Int i -> Const i
      | Ast.Bool b -> if b then Const 1 else Const 0
      | Ast.Var v -> Name (get_sym v)
      | Ast.Uop (uop, e) ->
          let addr = addr_of_expr e in
          let tmp = Temp (fresh ()) in
          CCVector.push code (op_of_uop uop, addr, Empty, tmp);
          tmp
      | Ast.Bop (bop, e1, e2) ->
          let addr1 = addr_of_expr e1 in
          let addr2 = addr_of_expr e2 in
          let tmp = Temp (fresh ()) in
          CCVector.push code (op_of_bop bop, addr1, addr2, tmp);
          tmp
      | Ast.Call (f, es) -> go_call f es (Temp (fresh ()))
    and go_call f es tmp =
      let addrs = List.map addr_of_expr es in
      List.iter
        (fun addr -> CCVector.push code (Param, addr, Empty, Empty))
        addrs;
      CCVector.push code (Call, Name (get_sym f), Const (List.length es), tmp);
      tmp
    and short_circuit t f = function
      | Ast.Uop (Ast.Not, e) -> short_circuit f t e
      | Ast.Bool b ->
          CCVector.push code (Goto, Const (if b then t else f), Empty, Empty)
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
          CCVector.push code (op_of_bop rel, addr1, addr2, Const t);
          CCVector.push code (Goto, Const f, Empty, Empty)
      | _ -> failwith "Invalid expression for short circuiting bool operation"
    and go_stmt next = function
      | Ast.Assign (v, e) ->
          let addr = addr_of_expr e in
          let s = get_sym v in
          CCVector.push code (Assign, addr, Empty, Name s)
      | Ast.Return e ->
          let addr =
            match Option.map addr_of_expr e with
            | Some addr -> addr
            | None -> Empty
          in
          CCVector.push code (Return, addr, Empty, Empty)
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
          CCVector.push code (Goto, Const next, Empty, Empty);
          label f;
          List.iter (go_stmt next) els
      | Ast.While (test, body) ->
          let begin_label = new_label () in
          let t = new_label () in
          label begin_label;
          short_circuit t next test;
          label t;
          List.iter (go_stmt begin_label) body;
          CCVector.push code (Goto, Const begin_label, Empty, Empty)
      | Ast.Call (f, es) -> ignore (go_call f es Empty)
    in
    List.iter
      (fun stmt ->
        let next = new_label () in
        go_stmt next stmt;
        label next)
      stmts;
    CCVector.map_in_place
      (function
        | Goto, Const l, Empty, Empty ->
            (Goto, Const (Hashtbl.find label_table l), Empty, Empty)
        | ((Eq | Ne | Gt | Ge | Lt | Le) as op), a, b, Const l ->
            (op, a, b, Const (Hashtbl.find label_table l))
        | c -> c)
      code;
    CCVector.push code (Nop, Empty, Empty, Empty);
    code
end
