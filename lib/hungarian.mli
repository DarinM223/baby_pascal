val min_to_max_cost : ?max_cost:int -> int array -> unit
(** Goes from minimum cost matching to maximum cost matching *)

val solve : cost:int array -> num_rows:int -> num_cols:int -> int array
(** Hungarian algorithm, does perfect matching only *)
