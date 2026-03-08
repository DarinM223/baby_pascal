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
let add_lengths length state =
  { state with distances = NameMap.map (fun d -> d + length) state.distances }
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
       and type Dom.position = int
       and type Dom.uid = X86.Cfg.uid) (graph : X86.Cfg.graph) : X86.Cfg.graph =
  (* edges leading out of loops:
     if u in loop_headers then header(v) != u else header(v) != header(u) *)
  (* each block has a unique length because critical edges are assumed
     to already be split and the only different case is edges leading out
     of loops, which must originate from nodes with multiple successors.
     That means that destination nodes must have only one predecessor if
     they are edges out of loops, otherwise its length is 0. *)
  let block_lengths =
    Array.init Loop.Dom.size @@ fun v ->
    let preds = Loop.Dom.predecessors v in
    match preds with
    | [ u ]
      when if Loop.(PositionSet.mem u loop_headers) then Loop.loop_header v <> u
           else Loop.(loop_header v <> loop_header u) ->
      m
    | _ -> 0
  in
  (* track current instruction number starting from 0
     then distance is num_instructions[block] - instruction number *)
  let _block_num_instructions =
    Array.init Loop.Dom.size @@ fun p ->
    let uid = X86.Cfg.idd (Loop.Dom.label_of_position p) in
    let (_, tail), _ = X86.Cfg.focus uid graph in
    count_instructions tail
  in
  let fact = fact () in
  let handle_instruction _a _i = failwith "" in
  let first_in = failwith "" in
  let middle_in = failwith "" in
  let last_in uid = function
    | X86.Printer.Exit -> fact.init_info
    | X86.Printer.Branch (i, (uid', _)) ->
      let block_length = block_lengths.(Loop.Dom.position_of_uid uid) in
      handle_instruction i @@ add_lengths block_length @@ fact.get uid'
    | X86.Printer.CBranch (i, (uid1, _), (uid2, _)) ->
      let block_length = block_lengths.(Loop.Dom.position_of_uid uid) in
      handle_instruction i @@ add_lengths block_length
      @@ fact.add_info (fact.get uid1) (fact.get uid2)
    | X86.Printer.Return i -> handle_instruction fact.init_info i
  in
  let analysis =
    (fact, { X86.Flow.BackwardAnalysis.first_in; middle_in; last_in })
  in
  let _ = X86.Flow.BackwardAnalysis.run analysis graph in
  failwith ""
