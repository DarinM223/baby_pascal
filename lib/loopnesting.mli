(** Loop nesting tree calculated using the algorithm from the paper "Testing
    Flow Graph Reducibility" *)

module type S = sig
  module Dom : Dominator.S
  module PositionSet : sig
    include CCSet.S with type elt = Dom.position
    val pp : t CCSet.printer
  end
  val loop_headers : PositionSet.t
  val loop_header : Dom.position -> Dom.position
  val loop_nodes : PositionSet.t array
end
module Make : functor
  (G : Graph.S)
  (Dom : Dominator.S
           with type label = G.label
            and type graph = G.graph
            and type position = int
            and type uid = G.uid)
  -> S with module Dom = Dom
