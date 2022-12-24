type typ = TInteger | TBoolean
type uop = Not
type bop = Add | Sub | Mul | And | Or | Eq | Neq | Lt | Le | Gt | Ge

type expr =
  | Int of int
  | Bool of bool
  | Var of string
  | Uop of uop * expr
  | Bop of bop * expr * expr
  | Call of string * expr list

type stmt =
  | Assign of string * expr
  | Return of expr option
  | If of expr * stmt list * stmt list
  | While of expr * stmt list
  | Call of string * expr list

type decl =
  | Function of string * (string * typ) list * typ * stmt list
  | Procedure of string * (string * typ) list * stmt list

type program = {
  globals : (string * typ) list;
  decls : decl list;
  main : stmt list;
}

let foo () =
  let open CCVector in
  let v = create_with ~capacity:100 0 in
  for i = 0 to 100 do
    push v i
  done;
  iter print_int v
