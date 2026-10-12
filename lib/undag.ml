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
    [@@deriving eq]
    let rec pp pp_instr fmt = function
      | Const c -> Format.fprintf fmt "$%d" c
      | Instr i -> Format.fprintf fmt "(%a)" pp_instr i
      | Reg r -> Format.fprintf fmt "%%%a" pp_reg r
      | Label (l, args) ->
        Format.fprintf fmt "%a(%a)" pp_label l
          (Format.pp_print_list ~pp_sep:Utils.pp_sep (pp pp_instr))
          args
    type 'a operand = 'a t [@@deriving show, eq]
    type 'a operands = 'a t list [@@deriving show, eq]
    let label l ops = Label (l, ops)
    let destruct_label = function
      | Label (l, ops) -> Some (l, ops)
      | _ -> None
    let tombstone = Normalize.Target.tombstone
    let is_tombstone = function
      | Reg reg -> Normalize.Target.Reg.is_tombstone reg
      | _ -> false
  end
  include Operand
  include Instruction.Make (Operand)
  let reg typ r = Reg (typ, Normalize.Target.name r)
end

module NameSet = Normalize.NameSet
module NameMap = Constprop.NameMap
module Cfg = Graph.Make (Target)
module Writer = struct
  module Target' = Instruction.Writer.Instruction.Make (Target.Operand) (Target)
  include Target'
  include Instruction.Writer.Graph.Make (Cfg) (Target')
end
module Converter =
  Instruction.Convert (Normalize.Target.Operand) (Target.Operand)
module Convert = Converter.Make (Normalize.Target) (Target)

open struct
  let increment = Option.fold ~none:(Some 1) ~some:(fun c -> Some (c + 1))
  let fold_uses f = Normalize.Target.fold_uses (fun acc use -> (f acc use, use))
  let clean_regs =
    List.filter (fun r -> not (Normalize.Target.Reg.is_tombstone r))
end

let treeify_instruction lookup instr =
  let rec convert_operand = function
    | Normalize.Target.Const i -> Target.Const i
    | Normalize.Target.Reg reg ->
      begin match lookup reg with
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

let treeify_block
    ?(rewrite =
      fun acc -> treeify_instruction (fun (_, r) -> NameMap.find_opt r acc)) map
    (first, tail) =
  let first =
    match first with
    | Normalize.Cfg.Entry -> Cfg.Entry
    | Normalize.Cfg.Label (l, info) ->
      Cfg.(Label (l, { local = info.local; args = clean_regs info.args }))
  in
  let rec rewrite_tail acc = function
    | Normalize.Cfg.Last Exit -> (acc, Cfg.Last Cfg.Exit)
    | Last (Branch (i, l)) ->
      let i = rewrite acc i in
      (acc, Cfg.(Last (Branch (i, l))))
    | Last (CBranch (i, l1, l2)) ->
      let i = rewrite acc i in
      (acc, Cfg.(Last (CBranch (i, l1, l2))))
    | Last (Normalize.Cfg.Return i) ->
      let i = rewrite acc i in
      (acc, Cfg.(Last (Return i)))
    | Tail (Instruction i, rest) ->
      let rewritten = rewrite acc i in
      let acc =
        NameSet.fold
          (fun def acc -> NameMap.add def rewritten acc)
          (Normalize.names_of_regs (Normalize.Target.defs i))
          acc
      in
      let acc, rest = rewrite_tail acc rest in
      (acc, Cfg.Tail (Instruction rewritten, rest))
  in
  let map, tail = rewrite_tail map tail in
  (map, (first, tail))

let treeify_graph (graph : Normalize.Cfg.graph) : Cfg.graph =
  let rpo = Normalize.Cfg.reverse_postorder_dfs graph in
  let go_block (acc, graph) block =
    let zblock = Normalize.Cfg.(goto_start (unzip block)) in
    let acc, (f, t) = treeify_block acc zblock in
    (acc, Cfg.(Blocks.insert (zip (First f, t)) graph))
  in
  snd (List.fold_left go_block (NameMap.empty, Cfg.empty) rpo)

module FreshGEP () : Normalize.Fresh = struct
  let c = ref (-1)
  let fresh typ =
    incr c;
    (typ, ("__gep_tmp", !c))
  let new_label () = failwith "Can't create label for getelementptr"
  let reset_names () = ()
  let reset_labels () = ()
end

let rec lower_getelementptr (module F : Normalize.Fresh) = function
  | Target.GetElementPtr (dest, typ, src, idxs) ->
    let new_tmp () = Target.Reg (F.fresh Ast.TInteger) in
    let rec go offset tmp = function
      | Ast.TPointer typ, (_, Target.Const idx) :: idxs ->
        go (offset + (idx * Ast.sizeof typ)) tmp (typ, idxs)
      | Ast.TArray (typ, size), (_, Target.Const idx) :: idxs
        when idx >= 0 && idx < size ->
        go (offset + (idx * Ast.sizeof typ)) tmp (typ, idxs)
      | (Ast.TPointer typ | Ast.TArray (typ, _)), (_, idx) :: idxs ->
        let sizeof = Ast.sizeof typ in
        (* offset += idx * sizeof(typ) *)
        let idx =
          if sizeof = 1 then idx
          else
            Target.Instr
              (Target.bop Ast.Mul ~dest:(new_tmp ()) ~src1:idx
                 ~src2:(Const sizeof))
        in
        let tmp =
          Target.Instr
            (Target.bop Ast.Add ~dest:(new_tmp ()) ~src1:tmp ~src2:idx)
        in
        go offset tmp (typ, idxs)
      | Ast.TRecord fields, (_, Target.Const idx) :: idxs ->
        let field, typ = List.nth fields idx in
        let offset' = Option.get (Ast.offsetof field fields) in
        go (offset + offset') tmp (typ, idxs)
      | _, [] ->
        begin match (offset, tmp) with
        | 0, Target.Instr instr -> instr
        | _ -> Target.bop Ast.Add ~dest ~src1:tmp ~src2:(Const offset)
        end
      | typ, _ ->
        failwith
        @@ Format.asprintf "lower_getelementptr: invalid type %a for lowering"
             Ast.pp_typ typ
    in
    go 0 src (typ, idxs)
  | instr ->
    instr
    |> Target.map_uses (function
      | Target.Instr instr -> Instr (lower_getelementptr (module F) instr)
      | op -> op)
    |> Target.map_defs (function
      | Target.Instr instr -> Instr (lower_getelementptr (module F) instr)
      | op -> op)

let undag (module F : Normalize.Fresh) ((first, tail) : Normalize.Cfg.block) :
    Cfg.block =
  let add_uses instr acc =
    let rec fold_operand acc = function
      | Normalize.Target.Reg (_, r) -> NameMap.update r increment acc
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
        begin match NameMap.find_opt (snd reg) !acc with
        | Some instr ->
          acc := NameMap.remove (snd reg) !acc;
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
    let instr = lower_getelementptr (module F) instr in
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
          (Normalize.names_of_regs (Normalize.Target.defs i))
          0
      in
      if num_uses <= 1 && not (Normalize.Target.is_side_effectful i) then
        let acc =
          NameSet.fold
            (fun def acc -> NameMap.add def rewritten acc)
            (Normalize.names_of_regs (Normalize.Target.defs i))
            acc
        in
        rewrite_tail acc rest
      else
        dump_mappings acc
        @@ Cfg.Tail (Instruction rewritten, rewrite_tail NameMap.empty rest)
  in
  let tail = rewrite_tail NameMap.empty tail in
  (first, tail)

let undag_graph cfg =
  let module F = FreshGEP () in
  Normalize.Cfg.Blocks.fold
    (fun _ block acc -> Cfg.Blocks.insert (undag (module F) block) acc)
    cfg Cfg.empty
