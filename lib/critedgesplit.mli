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
module Make : functor
  (_ : Normalize.Fresh)
  (G : Graph.S
         with type label = int * string
          and type Target.label = int * string)
  (_ : Graph.Extra
         with type label = G.label
          and type graph = G.graph
          and type position = int
          and type uid = G.uid)
  (_ : Requirements with module Target = G.Target)
  -> sig
  val split : G.graph -> G.graph
end
