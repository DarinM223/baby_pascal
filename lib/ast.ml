type typ =
  | TInteger
  | TBoolean
  | TVoid
  | TFunction of typ list * typ option
  | TPointer of typ
  | TRecord of typ list
  | TArray of typ * int
[@@deriving eq]

let rec pp_typ fmt = function
  | TInteger -> Format.fprintf fmt "int"
  | TBoolean -> Format.fprintf fmt "bool"
  | TVoid -> Format.fprintf fmt "void"
  | TFunction (args, ret) ->
    let pp_ret fmt = function
      | Some typ -> pp_typ fmt typ
      | None -> Format.fprintf fmt "void"
    in
    Format.fprintf fmt "(%a) -> %a"
      (Format.pp_print_list ~pp_sep:Utils.pp_sep pp_typ)
      args pp_ret ret
  | TPointer ptr -> Format.fprintf fmt "*%a" pp_typ ptr
  | TRecord _ -> Format.fprintf fmt ""
  | TArray (typ, size) -> Format.fprintf fmt "[%d]%a" size pp_typ typ

type uop = Not [@@deriving eq]
let pp_uop fmt = function
  | Not -> Format.fprintf fmt "!"

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
[@@deriving eq]

let pp_bop fmt = function
  | Add -> Format.fprintf fmt "+"
  | Sub -> Format.fprintf fmt "-"
  | Mul -> Format.fprintf fmt "*"
  | Div -> Format.fprintf fmt "/"
  | And -> Format.fprintf fmt "&&"
  | Or -> Format.fprintf fmt "||"
  | Eq -> Format.fprintf fmt "=="
  | Neq -> Format.fprintf fmt "!="
  | Lt -> Format.fprintf fmt "<"
  | Le -> Format.fprintf fmt "<="
  | Gt -> Format.fprintf fmt ">"
  | Ge -> Format.fprintf fmt ">="

module Make (T : sig
  type 'a t [@@deriving show, eq]
end) =
struct
  type expr' =
    | Int of int
    | Bool of bool
    | Var of string
    | Array of expr * int
    | Uop of uop * expr
    | Bop of bop * expr * expr
    | Deref of expr
    | ArrayIndex of expr * expr
    | Call of string * expr list
  and expr = expr' T.t [@@deriving show, eq]

  type stmt =
    | Assign of expr * expr
    | If of expr * stmt * stmt
    | While of expr * stmt
    | Call of string * expr list
    | Alloca of string * typ * int
    | Group of stmt list
  [@@deriving show, eq]
end

include Make (struct
  type 'a t = 'a [@@deriving show, eq]
end)

module Typed = Make (struct
  type 'a t = typ * 'a [@@deriving eq]
  let pp pp_reg fmt (typ, reg) =
    Format.fprintf fmt "%a:%a" pp_reg reg pp_typ typ
  let show pp_reg = Format.asprintf "%a" (pp pp_reg)
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

let rec sizeof (typ : typ) : int =
  match typ with
  | TInteger -> 8
  | TBoolean -> 1
  | TVoid -> 0
  | TFunction (_, _) -> failwith "Cannot get sizeof function"
  | TPointer _ -> 8
  | TRecord _ -> failwith "todo: calculate sizeof structures"
  | TArray (typ, size) -> sizeof typ * size
