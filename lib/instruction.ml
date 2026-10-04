module type Operand = sig
  type label [@@deriving show, eq]
  type 'a operand [@@deriving show, eq]
  type 'a operands = 'a operand list [@@deriving show, eq]
  val label : label -> 'a operands -> 'a operand
  val destruct_label : 'a operand -> (label * 'a operands) option
  val is_tombstone : 'a operand -> bool
end

module type Target = sig
  include Graph.Target
  val label : label -> operands -> operand
  val destruct_label : operand -> (label * operands) option
  val is_tombstone : operand -> bool
  val srcs : instr -> operands
  val dests : instr -> operands
  val fold_uses : ('a -> operand -> 'a * operand) -> 'a -> instr -> 'a * instr
  val map_uses : (operand -> operand) -> instr -> instr
  val fold_defs : ('a -> operand -> 'a * operand) -> 'a -> instr -> 'a * instr
  val map_defs : (operand -> operand) -> instr -> instr
  val is_side_effectful : instr -> bool
end

module Make (T : Operand) = struct
  type label = T.label
  type cond = Graph.Cond.t [@@deriving show, eq]
  let cond_of_bop = Graph.Cond.of_bop

  (* destination goes before sources for operands *)
  type instr =
    | Assign of operand * operand
    | Call of operand * operand * operands
    | Goto of T.label * operands
    | Cbranch of
        operand * operand * cond * T.label * operands * T.label * operands
    | Return of operands
    | Uop of operand * Ast.uop * operand
    | Bop of operand * Ast.bop * operand * operand
    (* Example: getelementptr { i32, ptr }, ptr @MyPtr, i64 0, i32 1 *)
    | GetElementPtr of operand * Ast.typ * operand * (Ast.typ * operand) list
    | Alloca of operand * int
    | Load of operand * operand
    | Store of operand * operand
  and operand = instr T.operand
  and operands = instr T.operands [@@deriving show, eq]

  let label = T.label
  let destruct_label = T.destruct_label
  let is_tombstone = T.is_tombstone

  let srcs = function
    | Call (_, o1, o2) -> o1 :: o2
    | Goto (l, args) -> [ T.label l args ]
    | Cbranch (o1, o2, _, l1, l1args, l2, l2args) ->
      [ T.label l1 l1args; T.label l2 l2args; o1; o2 ]
    | Return o -> o
    | Assign (_, o) | Uop (_, _, o) | Load (_, o) -> [ o ]
    | Bop (_, _, o1, o2) | Store (o1, o2) -> [ o1; o2 ]
    | Alloca _ -> []
    | GetElementPtr (_, _, o, tos) -> o :: List.map snd tos
  let dests = function
    | Assign (o, _) -> [ o ]
    | Call (o, _, _) -> [ o ]
    | Uop (o, _, _) -> [ o ]
    | Bop (o, _, _, _) -> [ o ]
    | Load (o, _) -> [ o ]
    | Alloca (o, _) -> [ o ]
    | Cbranch _ | Goto (_, _) | Return _ | Store _ -> []
    | GetElementPtr (o, _, _, _) -> [ o ]

  let fold_uses f acc =
    let f acc op = if T.is_tombstone op then (acc, op) else f acc op in
    function
    | Assign (d, s) ->
      let acc, s = f acc s in
      (acc, Assign (d, s))
    | Call (d, sf, s) ->
      let acc, sf = f acc sf in
      let acc, s = List.fold_left_map f acc s in
      (acc, Call (d, sf, s))
    | Goto (l, args) ->
      let acc, label = f acc (T.label l args) in
      begin match T.destruct_label label with
      | Some (l, args) -> (acc, Goto (l, args))
      | _ -> failwith "map_uses: goto label transformed into different operand"
      end
    | Cbranch (o1, o2, c, l1, l1args, l2, l2args) ->
      let acc, o1 = f acc o1 in
      let acc, o2 = f acc o2 in
      let acc, ol1 = f acc (T.label l1 l1args) in
      let acc, ol2 = f acc (T.label l2 l2args) in
      begin match (T.destruct_label ol1, T.destruct_label ol2) with
      | Some (l1, l1args), Some (l2, l2args) ->
        (acc, Cbranch (o1, o2, c, l1, l1args, l2, l2args))
      | _ ->
        failwith "map_uses: cbranch label transformed into different operand"
      end
    | Return o ->
      let acc, o = List.fold_left_map f acc o in
      (acc, Return o)
    | Uop (d, op, s) ->
      let acc, s = f acc s in
      (acc, Uop (d, op, s))
    | Bop (d, op, s1, s2) ->
      let acc, s1 = f acc s1 in
      let acc, s2 = f acc s2 in
      (acc, Bop (d, op, s1, s2))
    | Load (dest, addr) ->
      let acc, addr = f acc addr in
      (acc, Load (dest, addr))
    | Store (addr, v) ->
      let acc, addr = f acc addr in
      let acc, v = f acc v in
      (acc, Store (addr, v))
    | Alloca (dest, offset) -> (acc, Alloca (dest, offset))
    | GetElementPtr (dest, typ, ptr, typed_idxs) ->
      let acc, ptr = f acc ptr in
      let acc, typed_idxs =
        List.fold_left_map
          (fun acc (typ, idx) ->
            let acc, idx = f acc idx in
            (acc, (typ, idx)))
          acc typed_idxs
      in
      (acc, GetElementPtr (dest, typ, ptr, typed_idxs))
  let map_uses f i = snd (fold_uses (fun _ op -> ((), f op)) () i)
  let fold_defs f acc =
    let f acc op = if T.is_tombstone op then (acc, op) else f acc op in
    function
    | Assign (d, s) ->
      let acc, d = f acc d in
      (acc, Assign (d, s))
    | Call (d, sf, s) ->
      let acc, d = f acc d in
      (acc, Call (d, sf, s))
    | Uop (d, op, s) ->
      let acc, d = f acc d in
      (acc, Uop (d, op, s))
    | Bop (d, op, s1, s2) ->
      let acc, d = f acc d in
      (acc, Bop (d, op, s1, s2))
    | Load (d, s) ->
      let acc, d = f acc d in
      (acc, Load (d, s))
    | Alloca (d, offset) ->
      let acc, d = f acc d in
      (acc, Alloca (d, offset))
    | (Cbranch _ | Goto _ | Return _ | Store _) as op -> (acc, op)
    | GetElementPtr (d, typ, ptr, typed_idxs) ->
      let acc, d = f acc d in
      (acc, GetElementPtr (d, typ, ptr, typed_idxs))
  let map_defs f i = snd (fold_defs (fun _ op -> ((), f op)) () i)

  let assign ~dest ~src = Assign (dest, src)
  let call ~dest f es = Call (dest, f, es)
  let goto label args = Goto (label, args)
  let cbranch ~args (cond : cond) l1 l1args l2 l2args =
    match args with
    | [ o1; o2 ] -> Cbranch (o1, o2, cond, l1, l1args, l2, l2args)
    | _ -> failwith "cbranch expects only two arguments currently"
  let return ~uses = Return uses
  let uop op ~dest ~src = Uop (dest, op, src)
  let bop (op : Ast.bop) ~dest ~src1 ~src2 = Bop (dest, op, src1, src2)
end

module Writer = struct
  module Instruction = struct
    module Make (X : Operand) (I : module type of Make (X)) = struct
      include X
      include I
      let rec pp_operand op = X.pp_operand pp_instr op

      and pp_operands ops =
        Format.pp_print_list ~pp_sep:Utils.pp_sep pp_operand ops

      and pp_instr fmt = function
        | I.Assign (dest, src) ->
          Format.fprintf fmt "%a <- %a" pp_operand dest pp_operand src
        | Call (dest, f, args) ->
          Format.fprintf fmt "%a <- call %a %a" pp_operand dest pp_operand f
            pp_operands args
        | Goto (label, args) ->
          Format.fprintf fmt "goto %a %a" X.pp_label label pp_operands args
        | Cbranch (op1, op2, cond, thn, thn_args, els, els_args) ->
          Format.fprintf fmt "cbranch %a %a %a [then: %a %a] [else: %a %a]"
            pp_operand op1 Graph.Cond.pp cond pp_operand op2 X.pp_label thn
            pp_operands thn_args X.pp_label els pp_operands els_args
        | Return ops -> Format.fprintf fmt "  ret %a" pp_operands ops
        | Uop (dest, uop, src) ->
          Format.fprintf fmt "%a <- %a %a" pp_operand dest Ast.pp_uop uop
            pp_operand src
        | Bop (dest, bop, lhs, rhs) ->
          Format.fprintf fmt "%a <- %a %a %a" pp_operand dest pp_operand lhs
            Ast.pp_bop bop pp_operand rhs
        | GetElementPtr (dest, typ, src, args) ->
          let pp_arg fmt (typ, op) =
            Format.fprintf fmt "%a %a" Ast.pp_typ typ pp_operand op
          in
          Format.fprintf fmt "%a <- gep %a %a %a" pp_operand dest Ast.pp_typ typ
            pp_operand src
            (Format.pp_print_list ~pp_sep:Utils.pp_sep pp_arg)
            args
        | Alloca (dest, size) ->
          Format.fprintf fmt "%a <- alloca %d" pp_operand dest size
        | Load (dest, src) ->
          Format.fprintf fmt "%a <- load %a" pp_operand dest pp_operand src
        | Store (dest, src) ->
          Format.fprintf fmt "store %a %a" pp_operand dest pp_operand src
    end
    end
  module Graph = struct
    module Make
        (Cfg : Graph.S with type label = int * string)
        (Req : sig
          val pp_instr : Format.formatter -> Cfg.Target.instr -> unit
        end) =
    struct
      include Cfg
      let pp_label fmt (_, l) = Format.fprintf fmt "%s" l
      let pp_first fmt = function
        | Entry -> ()
        | Label (l, _info) -> Format.fprintf fmt "%a:" pp_label l
      let pp_middle fmt (Instruction instr) =
        Format.fprintf fmt "%a" Req.pp_instr instr
      let pp_last fmt = function
        | Exit | Return _ -> Format.fprintf fmt "ret"
        | Branch (i, _) | CBranch (i, _, _) ->
          Format.fprintf fmt "%a" Req.pp_instr i

      let rec pp_head state fmt = function
        | First f -> Format.fprintf fmt "%a@\n" pp_first f
        | Head (h, m) ->
          Format.fprintf fmt "%a  %a@\n" (pp_head state) h pp_middle m
      let rec pp_tail fmt = function
        | Last l -> Format.fprintf fmt "%a@\n" pp_last l
        | Tail (m, t) -> Format.fprintf fmt "%a@\n  %a" pp_middle m pp_tail t
      let pp_block fmt (f, t) =
        Format.fprintf fmt "%a@\n  %a" pp_first f pp_tail t
      let pp_graph fmt =
        Cfg.Blocks.iter (fun _ block -> Format.fprintf fmt "%a" pp_block block)
    end
  end
  end

module Convert (X : Operand) (Y : Operand with type label = X.label) = struct
  module type X' = module type of Make (X)
  module type Y' = module type of Make (Y)

  module Make (X' : X') (Y' : Y') = struct
    let convert f = function
      | X'.Assign (d, o) -> Y'.Assign (f d, f o)
      | X'.Call (d, fn, os) -> Y'.Call (f d, f fn, List.map f os)
      | X'.Goto (l, os) -> Y'.Goto (l, List.map f os)
      | X'.Cbranch (o1, o2, cond, l1, l1args, l2, l2args) ->
        Y'.Cbranch
          (f o1, f o2, cond, l1, List.map f l1args, l2, List.map f l2args)
      | X'.Return os -> Y'.Return (List.map f os)
      | X'.Uop (d, op, o) -> Y'.Uop (f d, op, f o)
      | X'.Bop (d, op, o1, o2) -> Y'.Bop (f d, op, f o1, f o2)
      | X'.Alloca (d, offset) -> Y'.Alloca (f d, offset)
      | X'.Load (d, o) -> Y'.Load (f d, f o)
      | X'.Store (o1, o2) -> Y'.Store (f o1, f o2)
      | X'.GetElementPtr (d, typ, o, tos) ->
        Y'.GetElementPtr (f d, typ, f o, List.map (CCPair.map_snd f) tos)
  end
end
