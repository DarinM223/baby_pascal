type typ =
  | TInteger
  | TBoolean
  | TVoid
  | TFunction of typ list * typ option
type uop = Not [@@deriving show, eq]
type bop =
  | Add
  | Sub
  | Mul
  | And
  | Or
  | Eq
  | Neq
  | Lt
  | Le
  | Gt
  | Ge
[@@deriving show, eq]

type expr =
  | Int of int
  | Bool of bool
  | Var of string
  | Uop of uop * expr
  | Bop of bop * expr * expr
  | Call of string * expr list

type stmt =
  | Assign of string * expr
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
