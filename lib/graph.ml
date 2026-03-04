include Graph_intf

module Make : Maker =
functor
  (Target : Target with type label = int * string)
  ->
  struct
    module Target = Target
    type uid = int [@@deriving show, eq]
    let entry_uid = 0

    type label = uid * string [@@deriving show, eq]
    type regs = Target.regs [@@deriving show, eq]

    type info = {
      local : bool;
      args : regs;
    }
    [@@deriving show, eq]

    type first =
      | Entry
      | Label of label * info
    [@@deriving show, eq]

    type middle = Instruction of Target.instr [@@deriving show, eq]

    type last =
      | Exit
      | Branch of Target.instr * label
      | CBranch of Target.instr * label * label
      | Return of Target.instr
    [@@deriving show, eq]

    type head =
      | First of first
      | Head of head * middle
    [@@deriving show, eq]

    type tail =
      | Last of last
      | Tail of middle * tail
    [@@deriving show, eq]

    type zblock = head * tail [@@deriving show, eq]
    type block = first * tail [@@deriving show, eq]

    type graph = block IntMap.t [@@deriving show, eq]
    type zgraph = zblock * graph [@@deriving show, eq]

    type nodes = zgraph -> zgraph

    let idd = function
      | None -> entry_uid
      | Some (uid, _) -> uid
    let id = function
      | Entry, _ -> entry_uid
      | Label ((uid, _), _), _ -> uid
    let block_label = function
      | Entry, _ -> None
      | Label (l, _), _ -> Some l
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

    let exit_uid graph =
      let rec find_exit = function
        | (uid, block) :: rest -> begin
          match goto_end (unzip block) with
          | _, Exit -> uid
          | _ -> find_exit rest
        end
        | [] -> failwith "exit not found"
      in
      find_exit (IntMap.to_list graph)

    let map_first f (head, tail) =
      let rec go head k =
        match head with
        | First first -> k (First (f first))
        | Head (head, mid) -> go head (fun head -> k (Head (head, mid)))
      in
      go head (fun head -> (head, tail))

    let rec map_last f (head, tail) =
      let rec go tail k =
        match tail with
        | Last last -> k (Last (f last))
        | Tail (mid, tail) -> go tail (fun tail -> k (Tail (mid, tail)))
      in
      go tail (fun tail -> (head, tail))

    let focus uid graph =
      let block = IntMap.find uid graph in
      (unzip block, IntMap.remove uid graph)

    let focus_entry graph = focus entry_uid graph
    let focus_exit graph =
      let uid = exit_uid graph in
      let zblock, graph = focus uid graph in
      let head, last = goto_end zblock in
      ((head, Last last), graph)

    module Blocks = struct
      let iter = IntMap.iter
      let filter = IntMap.filter
      let fold = IntMap.fold
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

      let prepare_for_splicing ?(entry = entry_uid) graph ~single ~multi =
        let (_, entry_tail), graph = focus entry graph in
        if IntMap.is_empty graph then
          match lastt entry_tail with
          | Exit -> single entry_tail
          | _ -> failwith "not a single exit block"
        else
          let exit_block, graph = focus_exit graph in
          let exit_head, exit_last = goto_end exit_block in
          match exit_last with
          | Exit -> multi ~entry:entry_tail ~exit:exit_head ~rest:graph
          | _ -> failwith "not a single exit graph"
    end

    let splice_head ?(entry = entry_uid) head graph =
      let single tail' =
        match ht_to_last head tail' with
        | head, Exit -> (empty, head)
        | _ -> failwith "spliced graph without exit"
      in
      let multi ~entry ~exit ~rest =
        (Blocks.insert (ht_to_first head entry) rest, exit)
      in
      prepare_for_splicing ~entry graph ~single ~multi

    let splice_tail ?(entry = entry_uid) graph tail =
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
      prepare_for_splicing ~entry graph ~single ~multi

    let splice_head_only head graph =
      let gentry, graph = focus_entry graph in
      match gentry with
      | First Entry, tail -> Blocks.insert (ht_to_first head tail) graph
      | _ -> failwith "graph to splice doesn't start with entry"

    let remove_entry graph =
      let gentry, graph = focus_entry graph in
      match gentry with
      | First Entry, tail -> (tail, graph)
      | _ -> failwith "removing nonexistent entry"

    let splice_focus_entry ((head, tail), blocks) graph =
      let tail, blocks' = splice_tail graph tail in
      ((head, tail), Blocks.union blocks' blocks)

    let splice_focus_exit ((head, tail), blocks) graph =
      let blocks', head = splice_head head graph in
      ((head, tail), Blocks.union blocks' blocks)

    let expand expand_middle expand_last graph =
      let rec expand_tail ((head, tail), blocks) =
        match tail with
        | Tail (middle, tail) ->
          expand_tail
            (splice_focus_exit ((head, tail), blocks) (expand_middle middle))
        | Last l -> Blocks.union (splice_head_only head (expand_last l)) blocks
      in
      let expand_block block expanded = expand_tail (unzip block, expanded) in
      IntMap.fold (fun _ -> expand_block) empty graph

    let successors = function
      | Exit -> []
      | Branch (_, l) -> [ l ]
      | CBranch (_, l1, l2) -> [ l1; l2 ]
      | Return _ -> []

    let reverse_postorder_dfs graph =
      let entry, blocks = focus_entry graph in
      let rec vnode block acc visited k =
        let u = id block in
        if IntSet.mem u visited then k acc visited
        else vchildren block (get_children block) acc (IntSet.add u visited) k
      and get_children block =
        block |> unzip |> last |> successors
        |> List.fold_left
             (fun acc (bid, _) ->
               try IntMap.find bid blocks :: acc with Not_found -> acc)
             []
      and vchildren block children acc visited k =
        let rec next children acc visited =
          match children with
          | [] -> k (block :: acc) visited
          | child :: children -> vnode child acc visited (next children)
        in
        next children acc visited
      in
      vnode (zip entry) [] IntSet.empty (fun acc _ -> acc)

    let instruction instr ((head, tail), graph) =
      ((head, Tail (Instruction instr, tail)), graph)

    let label ?(args = []) label ((head, tail), graph) =
      ( (head, Last (Branch (Target.goto label [], label))),
        Blocks.insert (Label (label, { local = false; args }), tail) graph )

    let unreachable = function
      | Last (Branch _ | Exit) -> ()
      | _ -> failwith "unreachable code"

    let branch ?(args = []) label ((head, tail), graph) =
      unreachable tail;
      ((head, Last (Branch (Target.goto label args, label))), graph)

    let cbranch ?(ifso_args = []) ?(ifnot_args = []) ~args cond ~ifso ~ifnot
        ((head, tail), graph) =
      unreachable tail;
      ( ( head,
          Last
            (CBranch
               ( Target.cbranch ~args cond ifso ifso_args ifnot ifnot_args,
                 ifso,
                 ifnot )) ),
        graph )

    let return ~uses ((head, tail), graph) =
      unreachable tail;
      ((head, Last (Return (Target.return ~uses))), graph)

    let exit ((head, tail), graph) =
      unreachable tail;
      ((head, Last Exit), graph)

    let precalculate_edges graph =
      let rpo = reverse_postorder_dfs graph in
      let module Extra = struct
        type label = Target.label
        type position = int [@@deriving show, eq]
        type graph = block IntMap.t
        let pp_label = pp_label
        let equal_label = equal_label
        let position_of_int p = p
        let int_of_position p = p
        let size = List.length rpo
        let label_of_position =
          let arr = Array.of_list (List.map block_label rpo) in
          fun pos -> arr.(pos)
        let position_of_label =
          let table = IntHashtbl.create size in
          List.iteri
            (fun i (first, _) ->
              let uid =
                match first with
                | Entry -> entry_uid
                | Label ((uid, _), _) -> uid
              in
              IntHashtbl.add table uid i)
            rpo;
          function
          | Some (uid, _) -> IntHashtbl.find table uid
          | None -> IntHashtbl.find table entry_uid

        let successors =
          let block_succs block =
            block |> unzip |> last |> successors
            |> List.map (fun l -> position_of_label (Some l))
          in
          let succs = Array.of_list (List.map block_succs rpo) in
          fun p -> succs.(p)

        let predecessors =
          let preds =
            Array.init size @@ fun num ->
            let result = ref IntSet.empty in
            for i = 0 to size - 1 do
              if List.mem num (successors i) then result := IntSet.add i !result
            done;
            !result
          in
          fun p -> IntSet.to_list preds.(p)

        let graph = graph
      end in
      (module Extra : Extra
        with type label = Target.label
         and type graph = graph)
  end
