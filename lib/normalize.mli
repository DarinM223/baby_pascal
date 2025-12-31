module Target : Graph.Target
module Cfg : Graph.S

val normalize : Ast.stmt list -> Cfg.graph
