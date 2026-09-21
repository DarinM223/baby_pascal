type typ =
  | TInteger
  | TBoolean
  | TVoid
  | TFunction of typ list * typ option
  | TPointer of typ
[@@deriving show, eq]
type uop = Not [@@deriving show, eq]
type bop =
  | Add
  | Sub
  | Mul
  | Div
  | And
  | Or
  | Eq
  | Neq
  | Lt
  | Le
  | Gt
  | Ge
[@@deriving show, eq]

module Make (T : sig
  type 'a t [@@deriving show, eq]
end) =
struct
  type expr' =
    | Int of int
    | Bool of bool
    | Var of string
    | Uop of uop * expr
    | Bop of bop * expr * expr
    | Load of expr
    | Call of string * expr list
  and expr = expr' T.t [@@deriving show, eq]

  type stmt =
    | Assign of string * expr
    | If of expr * stmt * stmt
    | While of expr * stmt
    | Call of string * expr list
    | Alloca of string * typ * int
    | Store of expr * expr
    | Group of stmt list
  [@@deriving show, eq]
end

include Make (struct
  type 'a t = 'a [@@deriving show, eq]
end)

module Typed = Make (struct
  type 'a t = typ * 'a [@@deriving show, eq]
end)

type 'a decl =
  | Function of string * (string * typ) list * typ * 'a
  | Procedure of string * (string * typ) list * 'a
[@@deriving show, eq]

type 'a program = {
  globals : (string * typ) list;
  decls : 'a decl list;
  main : 'a;
}
[@@deriving show, eq]
