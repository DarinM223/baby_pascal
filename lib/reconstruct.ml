module IntMap = Map.Make (Int)
module Make (G : Graph.S) (Dom : Dominator.S with type label = G.label) = struct
  module OperandSet = Set.Make (struct
    type t = G.Target.operand
    let compare = compare
  end)
  module OperandMap = Map.Make (struct
    type t = G.Target.operand
    let compare = compare
  end)
  let reconstruct (_fresh : unit -> G.Target.operand) (_old_defs : OperandSet.t)
      (_cloned_defs : OperandSet.t) (_graph : G.graph) : G.graph =
    (* todo: for every block in dominance frontier, place a phi with fresh definition *)
    (* todo: build substitution map *)
    let _df = Lazy.force Dom.dominator_frontier in
    failwith "still learning to code"
end
