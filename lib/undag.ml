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
    let label l ops = Label (l, ops)
    let destruct_label = function
      | Label (l, ops) -> Some (l, ops)
      | _ -> None
    let is_tombstone _ = false
  end
  include Operand
  include Instruction.Make (struct
    include Operand
    type 'a operand = 'a t [@@deriving show, eq]
    type 'a operands = 'a t list [@@deriving show, eq]
  end)
end

module NameSet = Normalize.NameSet
module NameMap = Constprop.NameMap
module Cfg = Graph.Make (Target)

let undag ((first, tail) : Normalize.Cfg.block) : Cfg.block =
  let add_uses (uses : NameSet.t) acc =
    NameSet.fold
      (fun use acc ->
        NameMap.update use
          (function
            | None -> Some 1
            | Some c -> Some (c + 1))
          acc)
      uses acc
  in
  let rec count_uses acc = function
    | Normalize.Cfg.Last l -> begin
      match l with
      | Normalize.Cfg.Exit -> acc
      | Normalize.Cfg.Branch (i, _) -> add_uses (Normalize.Target.uses i) acc
      | Normalize.Cfg.CBranch (i, _, _) ->
        add_uses (Normalize.Target.uses i) acc
      | Normalize.Cfg.Return i -> add_uses (Normalize.Target.uses i) acc
    end
    | Normalize.Cfg.Tail (Instruction i, rest) ->
      count_uses (add_uses (Normalize.Target.uses i) acc) rest
  in
  let count = count_uses NameMap.empty tail in
  (* todo: forward pass with map of variable->instruction *)
  (* if # of uses is <= 1, delete instruction *)
  failwith ""
