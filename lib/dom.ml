open Cfg

(*
  Code adapted from https://github.com/backtracking/ocamlgraph/blob/master/src/dominator.ml
*)

let dominators graph s0 =
  let size = M.cardinal graph in
  let nn = ref 0 in
  let bucket = Hashtbl.create size in
  let dfnum = Hashtbl.create size in
  let parent = Hashtbl.create size in
  let semi = Hashtbl.create size in
  let ancestor = Hashtbl.create size in
  let best = Hashtbl.create size in
  let samedom = Hashtbl.create size in
  let idom = Hashtbl.create size in
  let vertex = Array.make size s0 in
  let rec dfs p n =
    if not (Hashtbl.mem dfnum n) then (
      let enn = !nn in
      Hashtbl.add dfnum n enn;
      vertex.(enn) <- n;
      Option.iter (fun p -> Hashtbl.add parent n p) p;
      incr nn;
      S.iter
        (fun m -> if not (Hashtbl.mem dfnum m) then dfs (Some n) m)
        (M.find n graph).Block.succ)
  in
  dfs None s0;
  let lastn = !nn - 1 in
  let rec ancestor_with_lowest_semi v =
    try
      let a = Hashtbl.find ancestor v in
      let b = ancestor_with_lowest_semi a in
      Hashtbl.(replace ancestor v (find ancestor a));
      let best_v = Hashtbl.find best v in
      if Hashtbl.(find dfnum (find semi b) < find dfnum (find semi best_v)) then (
        Hashtbl.replace best v b;
        b)
      else best_v
    with Not_found -> Hashtbl.find best v
  in
  let link p n =
    Hashtbl.replace ancestor n p;
    Hashtbl.replace best n n
  in
  let semidominator n =
    let s = Hashtbl.find parent n in
    S.fold
      (fun v s ->
        try
          let s' =
            if Hashtbl.(find dfnum v <= find dfnum n) then v
            else Hashtbl.find semi (ancestor_with_lowest_semi v)
          in
          if Hashtbl.(find dfnum s' < find dfnum s) then s' else s
        with Not_found -> s)
      (M.find n graph).Block.pred s
  in
  while
    decr nn;
    !nn > 0
  do
    let n = vertex.(!nn) in
    let p = Hashtbl.find parent n in
    let s = semidominator n in
    Hashtbl.add semi n s;
    Hashtbl.add bucket s n;
    link p n;
    List.iter
      (fun v ->
        let y = ancestor_with_lowest_semi v in
        if Hashtbl.(find semi y = find semi v) then Hashtbl.add idom v p
        else Hashtbl.add samedom v y;
        Hashtbl.remove bucket p)
      (Hashtbl.find_all bucket p)
  done;
  for i = 1 to lastn do
    let n = vertex.(i) in
    try Hashtbl.(add idom n (find idom (find samedom n))) with Not_found -> ()
  done;
  Hashtbl.find idom

let dom_tree_of_idom graph idom =
  let tree = Hashtbl.create (M.cardinal graph) in
  M.iter
    (fun v _ -> try Hashtbl.add tree (idom v) v with Not_found -> ())
    graph;
  Hashtbl.find_all tree

let idoms idom x y = try x = idom y with Not_found -> false

let dominator_frontier graph dom_tree idom =
  let cache = Hashtbl.create 57 in
  let ( let* ) = ( @@ ) in
  let rec df n k =
    match Hashtbl.find_opt cache n with
    | Some r -> k r
    | None ->
        let s =
          List.filter
            (fun y -> not (idoms idom n y))
            (S.elements (M.find n graph).Block.succ)
        in
        let* r = add_df_ups s n (dom_tree n) in
        Hashtbl.add cache n r;
        k r
  and add_df_ups s n children k =
    match children with
    | [] -> k s
    | c :: cs ->
        let* dfc = df c in
        add_df_ups
          (List.fold_left
             (fun s w -> if idoms idom n w then s else w :: s)
             s dfc)
          n cs k
  in
  fun n -> df n (fun x -> x)