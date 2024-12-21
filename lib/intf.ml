module type Fresh = sig
  val fresh : unit -> int
  val reset : unit -> unit
end

module Fresh = struct
  module Make () = struct
    let counter = ref (-1)

    let fresh () =
      incr counter;
      !counter

    let reset () = counter := -1
  end
end

module type Sym = sig
  val get_sym : string -> int
  val get_name : int -> string
  val reset : unit -> unit
  val syms : unit -> int Seq.t
end

module Sym = struct
  module Make (Fresh : Fresh) : Sym = struct
    let string_to_sym = Hashtbl.create 1000
    let sym_to_string = Hashtbl.create 1000

    let get_sym name =
      match Hashtbl.find_opt string_to_sym name with
      | Some i -> i
      | None ->
        let tmp = Fresh.fresh () in
        Hashtbl.add string_to_sym name tmp;
        Hashtbl.add sym_to_string tmp name;
        tmp

    let get_name = Hashtbl.find sym_to_string

    let reset () =
      Fresh.reset ();
      Hashtbl.clear string_to_sym;
      Hashtbl.clear sym_to_string

    let syms () = Hashtbl.to_seq_keys sym_to_string
  end
end
