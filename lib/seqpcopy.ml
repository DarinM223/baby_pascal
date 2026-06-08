module type Requirements = sig
  module Target : Graph.Target
  val is_pcopy : Target.instr -> bool
  val temp : Target.operand
  val mov : dest:Target.operand -> src:Target.operand -> Target.instr
  val uses : Target.instr -> Target.operands
  val defs : Target.instr -> Target.operands
end
module SequentializePcopies
    (G : Graph.S)
    (Requirements : Requirements with module Target = G.Target) =
struct
  type status =
    | To_move
    | Being_moved
    | Moved

  (** Sequentializes a pcopy instruction and prepends a bunch of moves to the
      tail. `srcs` and `dests` are expected to be arrays of physical register
      operands, virtual registers should have already been colored at this
      point. *)
  let parallel_copy ~srcs ~dests temp tail =
    let n = Array.length srcs in
    let status = Array.make n To_move in
    let tail = ref tail in
    let rec move_one i =
      if srcs.(i) <> dests.(i) then begin
        status.(i) <- Being_moved;
        for j = 0 to n - 1 do
          if srcs.(j) = dests.(i) then
            match status.(j) with
            | To_move -> move_one j
            | Being_moved ->
              tail :=
                G.Tail
                  ( G.Instruction (Requirements.mov ~dest:temp ~src:srcs.(j)),
                    !tail );
              srcs.(j) <- temp
            | Moved -> ()
        done;
        tail :=
          G.Tail
            ( G.Instruction (Requirements.mov ~dest:dests.(i) ~src:srcs.(i)),
              !tail );
        status.(i) <- Moved
      end
    in
    for i = 0 to n - 1 do
      if status.(i) = To_move then move_one i
    done;
    !tail

  (** Takes a control flow graph and returns an updated control flow graph with
      all parallel copies sequentialized into moves *)
  let sequentialize cfg =
    let go_block _ block cfg =
      let head, tail = G.unzip block in
      let rec go_tail = function
        | G.Tail (Instruction i, tail) ->
          if Requirements.is_pcopy i then
            parallel_copy
              ~srcs:(Array.of_list (Requirements.uses i))
              ~dests:(Array.of_list (Requirements.defs i))
              Requirements.temp (go_tail tail)
          else go_tail tail
        | G.Last last -> G.Last last
      in
      let tail = go_tail tail in
      G.Blocks.insert (G.zip (head, tail)) cfg
    in
    G.Blocks.fold go_block cfg G.empty
end
