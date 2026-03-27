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

let undag ((first, tail) : Normalize.Cfg.block) : Cfg.block =
  let uses instr =
    let rec handle_operand = function
      | Normalize.Target.Reg r -> [ r ]
      | Normalize.Target.Label (_, args) -> List.concat_map handle_operand args
      | _ -> []
    in
    List.concat_map handle_operand (Normalize.Target.srcs instr)
  in
  let add_uses uses acc =
    List.fold_left
      (fun acc use ->
        NameMap.update use
          (function
            | None -> Some 1
            | Some c -> Some (c + 1))
          acc)
      acc uses
  in
  let rec count_uses acc = function
    | Normalize.Cfg.Last l ->
      begin match l with
      | Normalize.Cfg.Exit -> acc
      | Normalize.Cfg.Branch (i, _) -> add_uses (uses i) acc
      | Normalize.Cfg.CBranch (i, _, _) -> add_uses (uses i) acc
      | Normalize.Cfg.Return i -> add_uses (uses i) acc
      end
    | Normalize.Cfg.Tail (Instruction i, rest) ->
      count_uses (add_uses (uses i) acc) rest
  in
  let count = count_uses NameMap.empty tail in
  let clean_regs = List.filter (fun n -> not (Normalize.Name.is_tombstone n)) in
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
    | Normalize.Cfg.Last l ->
      begin match l with
      | Normalize.Cfg.Exit -> Cfg.Last Cfg.Exit
      | Normalize.Cfg.Branch (i, l) ->
        let i, acc = rewrite_instruction acc i in
        dump_mappings acc Cfg.(Last (Branch (i, l)))
      | Normalize.Cfg.CBranch (i, l1, l2) ->
        let i, acc = rewrite_instruction acc i in
        dump_mappings acc Cfg.(Last (CBranch (i, l1, l2)))
      | Normalize.Cfg.Return i ->
        let i, acc = rewrite_instruction acc i in
        dump_mappings acc Cfg.(Last (Return i))
      end
    | Normalize.Cfg.Tail (Instruction i, rest) ->
      let rewritten, acc = rewrite_instruction acc i in
      let num_uses =
        NameSet.fold
          (fun def acc ->
            acc + try NameMap.find def count with Not_found -> 0)
          (Normalize.Target.defs i) 0
      in
      if num_uses <= 1 && not (Constprop.is_side_effectful i) then
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
