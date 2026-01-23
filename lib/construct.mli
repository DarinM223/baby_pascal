type liveness = {
  live_in : Normalize.Cfg.uid -> Normalize.NameSet.t;
  live_out : Normalize.Cfg.uid -> Normalize.NameSet.t;
}
type a_orig = Normalize.Cfg.uid -> Normalize.NameSet.t

val calc_a_orig : Normalize.Flow.G.graph -> a_orig
val calc_live : Normalize.Flow.G.graph -> liveness

val insert_phis :
  (Normalize.Cfg.uid -> Normalize.Name.t -> bool) ->
  (module Dominator_intf.S with type label = Normalize.Cfg.label) ->
  a_orig ->
  Normalize.Cfg.graph ->
  Normalize.Cfg.graph
val insert_phis_minimal :
  (module Dominator_intf.S with type label = Normalize.Cfg.label) ->
  a_orig ->
  Normalize.Cfg.graph ->
  Normalize.Cfg.graph
val insert_phis_pruned :
  liveness ->
  (module Dominator_intf.S with type label = Normalize.Cfg.label) ->
  a_orig ->
  Normalize.Cfg.graph ->
  Normalize.Cfg.graph
val rename_variables :
  (module Dominator_intf.S with type label = Normalize.Cfg.label) ->
  Normalize.Cfg.graph ->
  Normalize.Cfg.graph
