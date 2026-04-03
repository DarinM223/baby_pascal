type t
(** type for a set container for union find operations *)

type repr
(** type of a representative of a set, being an abstract type for better type
    safety *)

val equal_repr : repr -> repr -> bool
(** check if two set representatives are equal *)

val create : int -> t
(** create a new union find set with given size *)

val union : t -> repr -> repr -> repr
(** merge two union find sets given the representatives of both sets *)

val find : t -> int -> repr
(** find the representative of a union find set given an element in the set *)

val size : t -> repr -> int
(** finds the number of elements in a set given the representative of a set *)
