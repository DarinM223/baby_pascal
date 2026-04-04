type t = int array
(** Represented as an array of integers. If the integer is negative, it doesn't
    point to a next element, and it represents the size of the equivalence
    class. If it is positive, it represents the index to the next element in the
    array. *)

type repr = int [@@deriving eq]

let to_int r = r

let create size = Array.make size (-1)

let union data set1 set2 =
  if set1 = set2 then set1
  else
    let d1 = data.(set1) in
    let d2 = data.(set2) in
    if d1 >= 0 || d2 >= 0 then
      failwith "union: expected set representatives to both be negative";
    let newcount = d1 + d2 in
    if d1 > d2 then begin
      data.(set1) <- set2;
      data.(set2) <- newcount;
      set2
    end
    else begin
      data.(set2) <- set1;
      data.(set1) <- newcount;
      set1
    end

let find data e =
  (* find representative *)
  let repr = ref e in
  while data.(!repr) >= 0 do
    repr := data.(!repr)
  done;
  let repr = !repr in
  let t = ref e in
  (* update links *)
  while !t <> repr do
    let next = data.(!t) in
    data.(!t) <- repr;
    t := next
  done;
  repr

let size data set = abs data.(set)
