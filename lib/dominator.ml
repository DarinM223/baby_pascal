include Dominator_intf

module Make : Maker =
functor
  (G : Graph.S)
  (Extra : Graph.Extra with type graph = G.graph)
  ->
  struct
    include Extra
    type tree =
      | Leaf of label option
      | Node of label option * tree list

    let idom = failwith ""
    let dominator_tree = failwith ""
    let dominator_frontier = failwith ""
  end
