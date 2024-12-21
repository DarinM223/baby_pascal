open Cfg

let crit_edge_split graph =
  let max_key = fst @@ M.max_binding graph in
  let fresh =
    let c = ref max_key in
    fun () ->
      incr c;
      !c
  in
  let graph =
    M.fold
      (fun n b graph ->
        S.fold
          (fun i graph ->
            let bi = M.find i graph in
            if S.cardinal bi.Block.succ > 1 then
              let j = fresh () in
              let bi' =
                {
                  (Block.create (CCVector.create ())) with
                  pred = S.singleton i;
                  succ = S.singleton n;
                }
              in
              let bi = { bi with succ = bi.succ |> S.remove n |> S.add j } in
              let b = Block.{ b with pred = b.pred |> S.remove i |> S.add j } in
              graph |> M.add i bi |> M.add j bi' |> M.add n b
            else
              graph)
          b.pred graph)
      graph graph
  in
  M.iter
    (fun _ b ->
      let preds =
        b.Block.pred |> S.elements |> List.map (fun p -> M.find p graph)
      in
      CCVector.iter
        (fun { Block.r = a0; ins = ais } ->
          List.iter2
            (fun ai pred -> CCVector.push pred.Block.pcopies (a0, ai))
            ais preds)
        b.phis;
      CCVector.clear_and_reset b.phis)
    graph;
  graph

let findi test v =
  let exception Break of int in
  try
    CCVector.iteri (fun i e -> if test e then raise (Break i)) v;
    raise Not_found
  with Break i -> i

module Make (Fresh : Intf.Fresh) = struct
  let seq_par_copies block =
    while not (CCVector.for_all (fun (b, a) -> a = b) block.Block.pcopies) do
      try
        let i =
          findi
            (fun (b, _) ->
              not (CCVector.exists (fun (_, b') -> b = b') block.pcopies))
            block.pcopies
        in
        let b, a = CCVector.get block.pcopies i in
        Code.push_quad block.code (Assign, a, Empty, b);
        CCVector.remove_unordered block.pcopies i
      with Not_found ->
        let i = findi (fun (b, a) -> a <> b) block.pcopies in
        let b, a = CCVector.get block.pcopies i in
        let a' =
          match a with
          | Code.Addr.Name (a, _) -> Code.Addr.Name (a, Fresh.fresh ())
          | _ -> a
        in
        (* TODO(DarinM223): Moves should be before the terminator jump in a block *)
        Code.push_quad block.code (Assign, a, Empty, a');
        CCVector.set block.pcopies i (b, a')
    done
end
