module type Operand = sig
  type label [@@deriving show, eq]
  type 'a operand [@@deriving show, eq]
  type 'a operands = 'a operand list [@@deriving show, eq]
  val label : label -> 'a operands -> 'a operand
  val destruct_label : 'a operand -> (label * 'a operands) option
  val is_tombstone : 'a operand -> bool
end

module Cond = struct
  type t =
    | LT
    | LE
    | GT
    | GE
    | EQ
    | NE
  [@@deriving show { with_path = false }, eq]

  let of_bop = function
    | Ast.Lt -> LT
    | Ast.Le -> LE
    | Ast.Gt -> GT
    | Ast.Ge -> GE
    | Ast.Eq -> EQ
    | Ast.Neq -> NE
    | _ -> failwith "Invalid binary operator"
end

module type Target = sig
  type label
  type cond = Cond.t [@@deriving show, eq]
  type operand
  type operands = operand list
  type instr
  val label : label -> operands -> operand
  val destruct_label : operand -> (label * operands) option
  val is_tombstone : operand -> bool
  val srcs : instr -> operands
  val dests : instr -> operands
  val map_uses : (operand -> operand) -> instr -> instr
  val map_defs : (operand -> operand) -> instr -> instr
end

module Make (T : Operand) = struct
  type label = T.label
  type cond = Cond.t [@@deriving show, eq]
  let cond_of_bop = Cond.of_bop

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
  and operand = instr T.operand
  and operands = instr T.operands [@@deriving show, eq]

  let label = T.label
  let destruct_label = T.destruct_label
  let is_tombstone = T.is_tombstone

  let srcs = function
    | Assign (_, o) -> [ o ]
    | Call (_, o1, o2) -> o1 :: o2
    | Goto (l, args) -> [ T.label l args ]
    | Cbranch (o1, o2, _, l1, l1args, l2, l2args) ->
      [ T.label l1 l1args; T.label l2 l2args; o1; o2 ]
    | Return o -> o
    | Uop (_, _, o) -> [ o ]
    | Bop (_, _, o1, o2) -> [ o1; o2 ]
  let dests = function
    | Assign (o, _) -> [ o ]
    | Call (o, _, _) -> [ o ]
    | Goto (_, _) -> []
    | Cbranch (_, _, _, _, _, _, _) -> []
    | Return _ -> []
    | Uop (o, _, _) -> [ o ]
    | Bop (o, _, _, _) -> [ o ]

  let map_uses f =
    let f op = if T.is_tombstone op then op else f op in
    function
    | Assign (d, s) -> Assign (d, f s)
    | Call (d, sf, s) ->
      let sf = f sf in
      Call (d, sf, List.map f s)
    | Goto (l, args) ->
      begin match T.destruct_label (f (T.label l args)) with
      | Some (l, args) -> Goto (l, args)
      | _ -> failwith "map_uses: goto label transformed into different operand"
      end
    | Cbranch (o1, o2, c, l1, l1args, l2, l2args) ->
      let o1 = f o1 in
      let o2 = f o2 in
      let ol1 = T.destruct_label (f (T.label l1 l1args)) in
      let ol2 = T.destruct_label (f (T.label l2 l2args)) in
      begin match (ol1, ol2) with
      | Some (l1, l1args), Some (l2, l2args) ->
        Cbranch (o1, o2, c, l1, l1args, l2, l2args)
      | _ ->
        failwith "map_uses: cbranch label transformed into different operand"
      end
    | Return o -> Return (List.map f o)
    | Uop (d, op, s) -> Uop (d, op, f s)
    | Bop (d, op, s1, s2) ->
      let s1 = f s1 in
      Bop (d, op, s1, f s2)
  let map_defs f =
    let f op = if T.is_tombstone op then op else f op in
    function
    | Assign (d, s) -> Assign (f d, s)
    | Call (d, sf, s) -> Call (f d, sf, s)
    | Goto (l, args) -> Goto (l, args)
    | Cbranch (o1, o2, c, l1, l1args, l2, l2args) ->
      Cbranch (o1, o2, c, l1, l1args, l2, l2args)
    | Return o -> Return o
    | Uop (d, op, s) -> Uop (f d, op, s)
    | Bop (d, op, s1, s2) -> Bop (f d, op, s1, s2)

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
  end
end
