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
  end
end
