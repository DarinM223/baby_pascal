open CCVector

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
[@@deriving show]

type addr = Const of int | Name of int | Temp of int | Empty [@@deriving show]
type quad = op * addr * addr * addr [@@deriving show]

type 'a node = {
  mutable value : 'a;
  pred : 'a node vector;
  next : 'a node vector;
}

type block = quad array

let counter = ref (-1)

let fresh () =
  incr counter;
  !counter

let sym_table = Hashtbl.create 1000

let get_sym sym =
  match Hashtbl.find_opt sym_table sym with
  | Some i -> i
  | None ->
      let tmp = fresh () in
      Hashtbl.add sym_table sym tmp;
      tmp

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

let normalize stmts =
  let len = List.length stmts in
  let code = create_with ~capacity:len (Nop, Empty, Empty, Empty) in
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
    | Ast.Var v -> Temp (get_sym v)
    | Ast.Uop (uop, e) ->
        let addr = addr_of_expr e in
        let tmp = Temp (fresh ()) in
        push code (op_of_uop uop, addr, Empty, tmp);
        tmp
    | Ast.Bop (bop, e1, e2) ->
        let addr1 = addr_of_expr e1 in
        let addr2 = addr_of_expr e2 in
        let tmp = Temp (fresh ()) in
        push code (op_of_bop bop, addr1, addr2, tmp);
        tmp
    | Ast.Call (f, es) -> go_call f es (Temp (fresh ()))
  and go_call f es tmp =
    let addrs = List.map addr_of_expr es in
    List.iter (fun addr -> push code (Param, addr, Empty, Empty)) addrs;
    push code
      (Call, Name (Hashtbl.find sym_table f), Const (List.length es), tmp);
    tmp
  and short_circuit t f = function
    | Ast.Uop (Ast.Not, e) -> short_circuit f t e
    | Ast.Bool b -> push code (Goto, Const (if b then t else f), Empty, Empty)
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
        push code (op_of_bop rel, addr1, addr2, Const t);
        push code (Goto, Const f, Empty, Empty)
    | _ -> failwith "Invalid expression for short circuiting bool operation"
  and go_stmt next = function
    | Ast.Assign (v, e) ->
        let addr = addr_of_expr e in
        let s = get_sym v in
        push code (Assign, addr, Empty, Temp s)
    | Ast.Return e ->
        let addr =
          match Option.map addr_of_expr e with
          | Some addr -> addr
          | None -> Empty
        in
        push code (Return, addr, Empty, Empty)
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
        push code (Goto, Const next, Empty, Empty);
        label f;
        List.iter (go_stmt next) els
    | Ast.While (test, body) ->
        let begin_label = new_label () in
        let t = new_label () in
        label begin_label;
        short_circuit t next test;
        label t;
        List.iter (go_stmt begin_label) body;
        push code (Goto, Const begin_label, Empty, Empty)
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
  push code (Nop, Empty, Empty, Empty);
  code

let identifying_leaders : quad vector -> block node = fun _ -> failwith "fuck"

type set = bytes

(*
  Stores gen/kill sets for the whole block and for each statement
  in the block (in order to recover the dataflow information
  of an individual statement).
*)
type gen_kill_info = {
  gen : set array;
  kill : set array;
  gen_block : set;
  kill_block : set;
}

let gen_kill : block -> gen_kill_info = fun _ -> failwith "fuck"