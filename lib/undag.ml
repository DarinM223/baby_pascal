module Target = struct
  type reg = Normalize.Target.reg [@@deriving show, eq]
  type regs = reg list [@@deriving show, eq]

  module Operand = struct
    type label = Normalize.Target.label [@@deriving show, eq]
    type 'a t =
      | Const of int
      | Instr of 'a
      | Reg of reg
      | Label of label * 'a t list
    [@@deriving show, eq]
    type 'a operand = 'a t [@@deriving show, eq]
    type 'a operands = 'a t list [@@deriving show, eq]
    let label l ops = Label (l, ops)
    let destruct_label = function
      | Label (l, ops) -> Some (l, ops)
      | _ -> None
    let tombstone = Reg Normalize.Name.tombstone
    let is_tombstone = function
      | Reg reg -> Normalize.Name.is_tombstone reg
      | _ -> false
  end
  include Operand
  include Instruction.Make (Operand)
  let reg r = Reg (Normalize.Target.name r)
end

module NameSet = Normalize.NameSet
module NameMap = Constprop.NameMap
module Cfg = Graph.Make (Target)
module Converter =
  Instruction.Convert (Normalize.Target.Operand) (Target.Operand)
module Convert = Converter.Make (Normalize.Target) (Target)

open struct
  let increment = Option.fold ~none:(Some 1) ~some:(fun c -> Some (c + 1))
  let fold_uses f = Normalize.Target.fold_uses (fun acc use -> (f acc use, use))
  let clean_regs = List.filter (fun n -> not (Normalize.Name.is_tombstone n))
end

let treeify ((first, tail) : Normalize.Cfg.block) : Cfg.block =
  let first =
    match first with
    | Normalize.Cfg.Entry -> Cfg.Entry
    | Normalize.Cfg.Label (l, info) ->
      Cfg.(Label (l, { local = info.local; args = clean_regs info.args }))
  in
  let rewrite_instruction acc instr =
    let rec convert_operand = function
      | Normalize.Target.Const i -> Target.Const i
      | Normalize.Target.Reg reg ->
        begin match NameMap.find_opt reg acc with
        | Some instr -> Target.Instr instr
        | None -> Target.Reg reg
        end
      | Normalize.Target.Label (l, ops) ->
        Target.Label
          ( l,
            List.filter_map
              (fun op ->
                if Normalize.Target.is_tombstone op then None
                else Some (convert_operand op))
              ops )
    in
    Convert.convert convert_operand instr
  in
  let rec rewrite_tail acc = function
    | Normalize.Cfg.Last Exit -> Cfg.Last Cfg.Exit
    | Last (Branch (i, l)) ->
      let i = rewrite_instruction acc i in
      Cfg.(Last (Branch (i, l)))
    | Last (CBranch (i, l1, l2)) ->
      let i = rewrite_instruction acc i in
      Cfg.(Last (CBranch (i, l1, l2)))
    | Last (Normalize.Cfg.Return i) ->
      let i = rewrite_instruction acc i in
      Cfg.(Last (Return i))
    | Tail (Instruction i, rest) ->
      let rewritten = rewrite_instruction acc i in
      let acc =
        NameSet.fold
          (fun def acc -> NameMap.add def rewritten acc)
          (Normalize.Target.defs i) acc
      in
      Cfg.Tail (Instruction rewritten, rewrite_tail acc rest)
  in
  let tail = rewrite_tail NameMap.empty tail in
  (first, tail)

let undag ((first, tail) : Normalize.Cfg.block) : Cfg.block =
  let add_uses instr acc =
    let rec fold_operand acc = function
      | Normalize.Target.Reg r -> NameMap.update r increment acc
      | Label (_, args) -> List.fold_left fold_operand acc args
      | _ -> acc
    in
    fst (fold_uses fold_operand acc instr)
  in
  let rec count_uses acc = function
    | Normalize.Cfg.Last Exit -> acc
    | Last (Branch (i, _) | CBranch (i, _, _) | Return i) -> add_uses i acc
    | Tail (Instruction i, rest) -> count_uses (add_uses i acc) rest
  in
  let count = count_uses NameMap.empty tail in
  let first =
    match first with
    | Normalize.Cfg.Entry -> Cfg.Entry
    | Normalize.Cfg.Label (l, info) ->
      Cfg.(Label (l, { local = info.local; args = clean_regs info.args }))
  in
  let rewrite_instruction acc instr =
    let acc = ref acc in
    let rec convert_operand = function
      | Normalize.Target.Const i -> Target.Const i
      | Normalize.Target.Reg reg ->
        begin match NameMap.find_opt reg !acc with
        | Some instr ->
          acc := NameMap.remove reg !acc;
          Target.Instr instr
        | None -> Target.Reg reg
        end
      | Normalize.Target.Label (l, ops) ->
        Target.Label
          ( l,
            List.filter_map
              (fun op ->
                if Normalize.Target.is_tombstone op then None
                else Some (convert_operand op))
              ops )
    in
    let instr = Convert.convert convert_operand instr in
    (instr, !acc)
  in
  let dump_mappings =
    NameMap.fold (fun _ instr tail -> Cfg.Tail (Instruction instr, tail))
  in
  let rec rewrite_tail acc = function
    | Normalize.Cfg.Last Exit -> Cfg.Last Cfg.Exit
    | Last (Branch (i, l)) ->
      let i, acc = rewrite_instruction acc i in
      dump_mappings acc Cfg.(Last (Branch (i, l)))
    | Last (CBranch (i, l1, l2)) ->
      let i, acc = rewrite_instruction acc i in
      dump_mappings acc Cfg.(Last (CBranch (i, l1, l2)))
    | Last (Normalize.Cfg.Return i) ->
      let i, acc = rewrite_instruction acc i in
      dump_mappings acc Cfg.(Last (Return i))
    | Tail (Instruction i, rest) ->
      let rewritten, acc = rewrite_instruction acc i in
      let num_uses =
        NameSet.fold
          (fun def acc ->
            acc + try NameMap.find def count with Not_found -> 0)
          (Normalize.Target.defs i) 0
      in
      if num_uses <= 1 && not (Normalize.Target.is_side_effectful i) then
        let acc =
          NameSet.fold
            (fun def acc -> NameMap.add def rewritten acc)
            (Normalize.Target.defs i) acc
        in
        rewrite_tail acc rest
      else
        dump_mappings acc
        @@ Cfg.Tail (Instruction rewritten, rewrite_tail NameMap.empty rest)
  in
  let tail = rewrite_tail NameMap.empty tail in
  (first, tail)
