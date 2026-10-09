type typ =
  | TInteger
  | TBoolean
  | TVoid
  | TFunction of typ list * typ option
  | TPointer of typ
  | TRecord of (string * typ) list
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
  | TRecord fields ->
    let pp_field fmt (name, typ) =
      Format.fprintf fmt "%s: %a" name pp_typ typ
    in
    Format.fprintf fmt "{%a}"
      (Format.pp_print_list ~pp_sep:Utils.pp_sep pp_field)
      fields
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
    | RecordField of expr * string
    | Call of string * expr list
  and expr = expr' T.t [@@deriving show, eq]

  type stmt =
    | Declare of string * typ
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

let rec alignof = function
  | TInteger -> 8
  | TBoolean -> 1
  | TVoid -> 0
  | TFunction (_, _) -> failwith "Cannot get alignof function yet"
  | TPointer _ -> 8
  | TRecord fields ->
    List.fold_left (fun acc (_, typ) -> max acc (alignof typ)) 0 fields
  | TArray (typ, _size) -> alignof typ

let rec sizeof = function
  | TInteger -> 8
  | TBoolean -> 1
  | TVoid -> 0
  | TFunction (_, _) -> failwith "Cannot get sizeof function yet"
  | TPointer _ -> 8
  | TRecord fields ->
    let rec go max_align offset = function
      | (_, typ) :: rest ->
        (* each field has to be padded to its alignment *)
        let alignment = alignof typ in
        let max_align = max max_align alignment in
        let remainder = offset mod alignment in
        if remainder = 0 then go max_align (offset + sizeof typ) rest
        else
          let offset = offset + alignment - remainder in
          go max_align (offset + sizeof typ) rest
      | [] ->
        (* struct itself is aligned with the maximum alignment of the fields
           has to be padded to that at the end of the struct *)
        let remainder = offset mod max_align in
        if remainder = 0 then offset else offset + max_align - remainder
    in
    go 0 0 fields
  | TArray (typ, size) -> sizeof typ * size

let offsetof field fields =
  let rec go offset = function
    | (field', typ) :: rest ->
      if String.equal field field' then Some offset
      else
        (* each field has to be padded to its alignment *)
        let alignment = alignof typ in
        let remainder = offset mod alignment in
        if remainder = 0 then go (offset + sizeof typ) rest
        else
          let offset = offset + alignment - remainder in
          go (offset + sizeof typ) rest
    | [] -> None
  in
  go 0 fields
