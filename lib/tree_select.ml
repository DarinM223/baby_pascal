open Code

type tree =
  | Addr of int * int
  | Int of int
  | Bop of op * tree * tree
  | Cbr of tree * int
  | Nop

let trees_of_code code =
  let stmts = CCVector.create_with ~capacity:(CCVector.length code) Nop in
  let nodes = Hashtbl.create (CCVector.length code) in
  let operand = function
    | Addr.Temp t -> Hashtbl.find nodes t
    | Name (a, b) -> Addr (a, b)
    | Const i -> Int i
    | Empty -> Nop
  in
  CCVector.iter
    (function
      | { op = Assign; a; b = Empty; r = Name (n, i) } ->
          CCVector.push stmts (Bop (Assign, Addr (n, i), operand a))
      | { op; a; b; r = Empty } ->
          CCVector.push stmts (Bop (op, operand a, operand b))
      | { op; a; b; r = Const i } ->
          CCVector.push stmts (Cbr (Bop (op, operand a, operand b), i))
      | { op; a; b; r = Temp t } ->
          Hashtbl.add nodes t (Bop (op, operand a, operand b))
      | { op; a; b; r = Name (n, i) } ->
          CCVector.push stmts
            (Bop (Assign, Addr (n, i), Bop (op, operand a, operand b))))
    code;
  CCVector.to_array stmts

(*
let match_stmt = function
  | Bop (Assign, Addr (r, i), n) -> failwith ""
  | Bop (Goto, Int i, Nop) -> failwith ""

and match_expr = function
  | Bop (Add, a, b) -> failwith ""
  | Bop (Sub, a, b) -> failwith ""
  | Bop (Mul, a, b) -> failwith ""
*)

let example1 =
  [|
    (Mul, Const 2, Const 3, Temp 0);
    (Add, Const 1, Temp 0, Temp 1);
    (Assign, Temp 1, Empty, name 2);
    (Eq, name 2, Const 1, Const 5);
    (Goto, Const 15, Empty, Empty);
    (Lt, name 2, Const 5, Const 7);
    (Goto, Const 15, Empty, Empty);
    (Eq, name 2, Const 1, Const 9);
    (Goto, Const 16, Empty, Empty);
    (Lt, name 2, Const 5, Const 11);
    (Goto, Const 16, Empty, Empty);
    (Add, name 2, Const 1, Temp 3);
    (Assign, Temp 3, Empty, name 2);
    (Goto, Const 7, Empty, Empty);
    (Goto, Const 16, Empty, Empty);
    (Assign, Const 60, Empty, name 4);
    (Nop, Empty, Empty, Empty);
  |]
  |> Array.map (fun (op, a, b, r) -> { op; a; b; r })

let result = trees_of_code (CCVector.of_array example1)