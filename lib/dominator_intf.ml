module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)

module type S = sig
  include Graph.Extra
  type tree =
    | Leaf of label option
    | Node of label option * tree list
  val pp_tree : Format.formatter -> tree -> unit
  val show_tree : tree -> string

  val idom : position -> position
  val dominator_tree : tree Lazy.t
  val dominator_frontier : (position -> position list) Lazy.t
end

module type Maker = functor
  (G : Graph.S)
  (_ : Graph.Extra with type label = G.label and type graph = G.graph)
  -> S with type label = G.label and type graph = G.graph

module type Intf = sig
  module type S = S
  module Make : Maker
end
