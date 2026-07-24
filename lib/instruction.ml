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
    | Goto (l, args) -> (acc, Goto (l, args))
    | Cbranch (o1, o2, c, l1, l1args, l2, l2args) ->
      (acc, Cbranch (o1, o2, c, l1, l1args, l2, l2args))
    | Return o -> (acc, Return o)
    | Uop (d, op, s) ->
      let acc, d = f acc d in
      (acc, Uop (d, op, s))
    | Bop (d, op, s1, s2) ->
      let acc, d = f acc d in
      (acc, Bop (d, op, s1, s2))
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
