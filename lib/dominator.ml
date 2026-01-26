include Dominator_intf

module Make : Maker =
functor
  (G : Graph.S)
  (Extra : Graph.Extra with type label = int * string and type graph = G.graph)
  ->
  struct
    include Extra
    type tree =
      | Leaf of label option
      | Node of label option * tree list
    [@@deriving show, eq]

    type node_type =
      | Undefined
      | Defined of Extra.position
    [@@deriving show]
    let idom = Array.make Extra.size Undefined
    let set_doms pos v = idom.(Extra.int_of_position pos) <- Defined v
    let doms pos =
      match idom.(Extra.int_of_position pos) with
      | Defined pos -> pos
      | Undefined -> raise Not_found
    let intersect b1 b2 =
      let finger1 = ref b1 in
      let finger2 = ref b2 in
      while !finger1 <> !finger2 do
        while !finger1 > !finger2 do
          finger1 := doms !finger1
        done;
        while !finger2 > !finger1 do
          finger2 := doms !finger2
        done
      done;
      !finger1

    let idom =
      let changed = ref true in
      set_doms (Extra.position_of_label None) (Extra.position_of_label None);
      let go_block block =
        let block_pos = Extra.position_of_label (G.block_label block) in
        match Extra.predecessors block_pos with
        | p :: ps ->
          let fold_predecessor acc pred =
            try
              ignore (doms pred);
              intersect pred acc
            with Not_found -> acc
          in
          let new_idom = List.fold_left fold_predecessor p ps in
          let should_update =
            try doms block_pos <> new_idom with Not_found -> true
          in
          if should_update then begin
            set_doms block_pos new_idom;
            changed := true
          end
        | _ -> ()
      in
      let rpo = G.reverse_postorder_dfs Extra.graph in
      while !changed do
        changed := false;
        List.iter go_block rpo
      done;
      doms

    let dominator_tree =
      lazy begin
        let children_mapping = Array.make Extra.size IntSet.empty in
        let add_children block =
          let parent = Extra.int_of_position (idom block) in
          children_mapping.(parent) <-
            IntSet.add (Extra.int_of_position block) children_mapping.(parent)
        in
        let rec build_tree node k =
          let children =
            children_mapping.(Extra.int_of_position node)
            |> IntSet.to_list
            |> List.map Extra.position_of_int
            |> List.filter (fun p -> p <> node)
          in
          let rec go acc children =
            match children with
            | [] -> k (Node (Extra.label_of_position node, List.rev acc))
            | c :: cs -> build_tree c (fun tree -> go (tree :: acc) cs)
          in
          match children with
          | [] -> k (Leaf (Extra.label_of_position node))
          | _ -> go [] children
        in
        IntMap.iter
          (fun _ block ->
            block |> G.block_label |> Extra.position_of_label |> add_children)
          Extra.graph;
        build_tree (Extra.position_of_label None) (fun t -> t)
      end

    let dominator_frontier =
      lazy begin
        let frontier = Array.make Extra.size IntSet.empty in
        let go block_pos =
          let preds = Extra.predecessors block_pos in
          let add_to_frontier pos n =
            let pos = Extra.int_of_position pos in
            frontier.(pos) <-
              IntSet.add (Extra.int_of_position n) frontier.(pos)
          in
          let go_pred p =
            let runner = ref p in
            while !runner <> idom block_pos do
              add_to_frontier !runner block_pos;
              runner := idom !runner
            done
          in
          if List.length preds >= 2 then List.iter go_pred preds
        in
        IntMap.iter
          (fun _ block -> go (Extra.position_of_label (G.block_label block)))
          graph;
        fun p ->
          frontier.(Extra.int_of_position p)
          |> IntSet.to_list
          |> List.map Extra.position_of_int
      end
  end
