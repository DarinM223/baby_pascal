module InstrHashtbl = Hashtbl.Make (struct
  type t = Normalize.Target.instr
  let equal = Normalize.Target.equal_instr
  let hash = Hashtbl.hash
end)

module ValueNumbering (Dom : Dominator.S with type label = Normalize.Cfg.label) =
struct
  type state = {
    instr_of_vn : Normalize.Target.instr array;
        (** Used for instruction simplification *)
    vn : int array;  (** Value number of variable *)
    vn_of_expr : int InstrHashtbl.t;
        (** Hashtable for getting value number from hashed instruction *)
  }

  let rec dvnt (state : state) (tree : Dom.tree) (graph : Normalize.Cfg.graph) :
      Normalize.Cfg.graph =
    let keys = CCVector.create () in
    let zblock, graph =
      Normalize.Cfg.(focus (idd (Dom.tree_label tree)) graph)
    in
    (* todo: perform value numbering here *)
    let graph = Normalize.Cfg.unfocus (zblock, graph) in
    let graph =
      List.fold_left (Fun.flip (dvnt state)) graph (Dom.tree_children tree)
    in
    (* Pop newly added expressions in scope *)
    CCVector.iter (InstrHashtbl.remove state.vn_of_expr) keys;
    graph
end
