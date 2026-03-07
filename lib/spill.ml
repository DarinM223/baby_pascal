let m = 10_000

module IntHashtbl = Hashtbl.Make (Int)
module NameMap = Constprop.NameMap

let count_instructions (tail : X86.Cfg.tail) =
  let rec go acc = function
    | X86.Printer.Last _ -> acc
    | X86.Printer.Tail (_, t) -> go (acc + 1) t
  in
  go 1 tail

type state = {
  distances : int NameMap.t;
  (* temporary for each block *)
  first_use : int NameMap.t;
  count : int;
}
let hashtbl_size = 100
let fact () =
  let store = IntHashtbl.create hashtbl_size in
  (* if variable doesn't exist in distances map it has distance of infinity *)
  let init_info =
    { distances = NameMap.empty; first_use = NameMap.empty; count = 0 }
  in
  {
    X86.Flow.init_info;
    add_info =
      (fun a b ->
        {
          init_info with
          distances =
            NameMap.union
              (fun _ v1 v2 -> Some (min v1 v2))
              a.distances b.distances;
        });
    changed = (fun ~before ~after -> before.distances <> after.distances);
    skip_block = Fun.const false;
    get = IntHashtbl.find store;
    set = IntHashtbl.replace store;
  }

let next_use_distances
    (module Loop : Loopnesting.S
      with type Dom.label = X86.Cfg.label
       and type Dom.position = int) (graph : X86.Cfg.graph) : X86.Cfg.graph =
  let _block_lengths = Array.make Loop.Dom.size 0 in
  (* todo: track current instruction number starting from 0
     then distance is num_instructions[block] - instruction number *)
  let _block_num_instructions =
    Array.init Loop.Dom.size @@ fun p ->
    let uid = X86.Cfg.idd (Loop.Dom.label_of_position p) in
    let (_, tail), _ = X86.Cfg.focus uid graph in
    count_instructions tail
  in
  let fact = fact () in
  let first_in = failwith "" in
  let middle_in = failwith "" in
  (* edges leading out of loops: header(block) != header(succ) *)
  let last_in _uid = function
    | X86.Printer.Exit -> failwith ""
    | X86.Printer.Branch (_, _) -> failwith ""
    | X86.Printer.CBranch (_, _, _) -> failwith ""
    | X86.Printer.Return _ -> failwith ""
  in
  let analysis =
    (fact, { X86.Flow.BackwardAnalysis.first_in; middle_in; last_in })
  in
  let _ = X86.Flow.BackwardAnalysis.run analysis graph in
  failwith ""
