module type S = sig
  module G : Graph.S

  type 'a fact = {
    init_info : 'a;
    add_info : 'a -> 'a -> 'a;
    changed : before:'a -> after:'a -> bool;
    get : G.uid -> 'a;
    set : G.uid -> 'a -> unit;
  }

  type 'a answer =
    | Dataflow of 'a
    | Rewrite of G.graph

  val run :
    'a fact -> bool ref -> 'a -> (G.block -> unit) -> G.block list -> int

  module BackwardAnalysis : sig
    type 'a functions = {
      first_in : 'a -> G.first -> 'a;
      middle_in : 'a -> G.middle -> 'a;
      last_in : G.last -> 'a;
    }
    type 'a t = 'a fact * 'a functions
    val run : 'a fact * 'a functions -> G.graph -> int
  end

  module BackwardPass : sig
    type 'a functions = {
      first_in : 'a -> G.first -> 'a answer;
      middle_in : 'a -> G.middle -> 'a answer;
      last_in : G.last -> 'a answer;
    }
    type 'a t = 'a fact * 'a functions
    val solve_graph : 'a t -> G.graph -> 'a -> 'a
    val solve_and_rewrite :
      'a t -> G.graph -> 'a -> bool -> 'a * (G.graph * bool)
  end
end

module type Maker = functor (G : Graph.S) -> S with module G = G

module type Intf = sig
  module type S = S
  module Make : Maker
end
