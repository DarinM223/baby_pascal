module type Target = sig
  type label
  type reg
  type instr

  type cond =
    | LT
    | LE
    | GT
    | GE
    | EQ
    | NE

  val goto : label -> instr
  val cbranch : uses:reg list -> cond -> label -> label -> instr
  val return : uses:reg list -> instr
end

module IntMap = Map.Make (Int)

module Graph = struct
  module Make (Target : Target) = struct
    module Target = Target
    type uid = int
    let entry_uid = 0

    type label = uid * string
    type regs = Target.reg list

    type local = Local of bool
    type first =
      | Entry
      | Label of label * local
    type middle = Instruction of Target.instr
    type last =
      | Exit
      | Branch of Target.instr * label
      | CBranch of Target.instr * label * label
      | Return of Target.instr * regs

    type head =
      | First of first
      | Head of head * middle
    type tail =
      | Last of last
      | Tail of middle * tail

    type zblock = head * tail
    type block = first * tail

    type graph = block IntMap.t
    type zgraph = zblock * graph

    let id = function
      | Entry, _ -> entry_uid
      | Label ((uid, _), _), _ -> uid
    let empty = IntMap.singleton entry_uid (Entry, Last Exit)

    let rec zip = function
      | First first, tail -> (first, tail)
      | Head (head, mid), tail -> zip (head, Tail (mid, tail))

    let unzip (first, tail) = (First first, tail)

    let rec firstt = function
      | First f -> f
      | Head (h, _) -> firstt h
    let first (h, _) = firstt h

    let rec lastt = function
      | Last l -> l
      | Tail (_, t) -> lastt t
    let last (_, t) = lastt t

    let goto_start = zip
    let rec goto_end = function
      | head, Last last -> (head, last)
      | head, Tail (mid, tail) -> goto_end (Head (head, mid), tail)

    let focus uid graph =
      let block = IntMap.find uid graph in
      (unzip block, IntMap.remove uid graph)

    let entry graph = focus entry_uid graph
    let exit graph =
      let rec find_exit = function
        | (uid, block) :: rest -> begin
          match goto_end (unzip block) with
          | _, Exit -> uid
          | _ -> find_exit rest
        end
        | [] -> failwith "exit not found"
      in
      let uid = find_exit (IntMap.to_list graph) in
      let zblock, graph = focus uid graph in
      let head, last = goto_end zblock in
      ((head, Last last), graph)

    module Blocks = struct
      let insert block =
        match block with
        | Entry, _ -> IntMap.add entry_uid block
        | Label ((uid, _), _), _ -> IntMap.add uid block
      let union graph1 graph2 = IntMap.union (fun _ a _ -> Some a) graph1 graph2
    end

    let unfocus (zblock, graph) = Blocks.insert (zip zblock) graph

    open struct
      let rec ht_to_first head tail =
        match head with
        | First f -> (f, tail)
        | Head (h, m) -> ht_to_first h (Tail (m, tail))
      let rec ht_to_last head tail =
        match tail with
        | Last l -> (head, l)
        | Tail (m, l) -> ht_to_last (Head (head, m)) l

      let prepare_for_splicing graph ~single ~multi =
        let (_, entry_tail), graph = entry graph in
        if IntMap.is_empty graph then
          match lastt entry_tail with
          | Exit -> single entry_tail
          | _ -> failwith "not a single exit block"
        else
          let exit_block, graph = exit graph in
          let exit_head, exit_last = goto_end exit_block in
          match exit_last with
          | Exit -> multi ~entry:entry_tail ~exit:exit_head ~rest:graph
          | _ -> failwith "not a single exit graph"
    end

    let splice_head head graph =
      let single tail' =
        match ht_to_last head tail' with
        | head, Exit -> (empty, head)
        | _ -> failwith "spliced graph without exit"
      in
      let multi ~entry ~exit ~rest =
        (Blocks.insert (ht_to_first head entry) rest, exit)
      in
      prepare_for_splicing graph ~single ~multi

    let splice_tail graph tail =
      let single tail' =
        match ht_to_last (First Entry) tail' with
        | head, Exit -> begin
          match ht_to_first head tail with
          | Entry, tail'' -> (tail'', empty)
          | _ -> failwith "impossible, head is not an entry"
        end
        | _ -> failwith "spliced graph without exit"
      in
      let multi ~entry ~exit ~rest =
        (entry, Blocks.insert (ht_to_first exit tail) rest)
      in
      prepare_for_splicing graph ~single ~multi
  end
end
