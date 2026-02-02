module IntHashtbl = Hashtbl.Make (Int)
module Flow = Normalize.Flow
module Name = Normalize.Name
module NameMap = struct
  include CCMap.Make (struct
    include Name
    let compare = compare
  end)
  let pp pp_v = pp Name.pp pp_v
end

type lattice =
  | NeverDefined
  | Defined of int
  | OverDefined
[@@deriving show, eq]

type t = {
  mapping : lattice NameMap.t;
  executable : bool;
}
[@@deriving show, eq]

let hashtbl_size = 100
let state_fact () =
  let store = IntHashtbl.create hashtbl_size in
  {
    Flow.init_info = { mapping = NameMap.empty; executable = false };
    add_info =
      (fun a b ->
        {
          mapping = NameMap.union (fun _ _ a -> Some a) a.mapping b.mapping;
          executable = b.executable;
        });
    changed = (fun ~before ~after -> not (equal before after));
    skip_block = (fun uid -> not (IntHashtbl.find store uid).executable);
    get = IntHashtbl.find store;
    set = IntHashtbl.add store;
  }
