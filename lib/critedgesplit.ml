module type Requirements = sig
  module Target : Graph.Target
  val label : Target.label -> Target.operand list -> Target.operand
  val destruct_label :
    Target.operand -> (Target.label * Target.operand list) option
  val fold_uses :
    ('a -> Target.operand -> 'a * Target.operand) ->
    'a ->
    Target.instr ->
    'a * Target.instr
end

let hashtbl_size = 100

module Make
    (Fresh : Normalize.Fresh)
    (G :
      Graph.S
        with type label = int * string
         and type Target.label = int * string)
    (Extra :
      Graph.Extra
        with type label = G.label
         and type graph = G.graph
         and type position = int
         and type uid = G.uid)
    (Requirements : Requirements with module Target = G.Target) =
struct
  module LabelTbl = CCHashtbl.Make (struct
    type t = G.label
    let equal = G.equal_label
    let hash = G.hash_label
  end)
  let split cfg =
    let go _uid block cfg =
      let head, last = G.(goto_end (unzip block)) in
      let last, cfg =
        match last with
        | G.Exit | G.Branch _ | G.Return _ -> (last, cfg)
        | G.CBranch (instr, l1, l2) ->
          let subst = LabelTbl.create hashtbl_size in
          let cfg, instr =
            Requirements.fold_uses
              (fun cfg op ->
                match Requirements.destruct_label op with
                | Some (l, ops)
                  when (G.equal_label l l1 || G.equal_label l l2)
                       && List.length
                            Extra.(predecessors (position_of_label (Some l)))
                          > 1 ->
                  let l' =
                    try LabelTbl.find subst l
                    with Not_found ->
                      let l' = Fresh.new_label () in
                      LabelTbl.add subst l l';
                      l'
                  in
                  let head =
                    G.(First (Label (l', { local = true; args = [] })))
                  in
                  let tail = G.(Last (Branch (G.Target.goto l ops, l))) in
                  let block = G.zip (head, tail) in
                  let cfg = G.Blocks.insert block cfg in
                  (cfg, Requirements.label l' [])
                | _ -> (cfg, op))
              cfg instr
          in
          let last =
            G.CBranch
              ( instr,
                LabelTbl.get_or subst l1 ~default:l1,
                LabelTbl.get_or subst l2 ~default:l2 )
          in
          (last, cfg)
      in
      G.unfocus ((head, Last last), cfg)
    in
    G.Blocks.fold go cfg G.empty
end
