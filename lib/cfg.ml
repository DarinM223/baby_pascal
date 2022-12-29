open Code
module S = Set.Make (Int)
module M = Map.Make (Int)

module Block = struct
  type t = { code : quad CCVector.vector; pred : S.t; succ : S.t }

  let pp fmt block =
    Format.fprintf fmt "{ code = %s; pred = %s; succ = %s }"
      ([%show: quad array] (CCVector.to_array block.code))
      ([%show: int list] (S.elements block.pred))
      ([%show: int list] (S.elements block.succ))

  let equal a b =
    CCVector.(to_array a.code = to_array b.code)
    && S.equal a.pred b.pred && S.equal a.succ b.succ

  let entry, exit = (-1, -2)
end

let blocks_of_code code =
  let identify_leaders code =
    let leaders = ref (S.singleton 0) in
    CCVector.iteri
      (fun i -> function
        | Goto, Const j, _, _ | (Eq | Ne | Lt | Le | Gt | Ge), _, _, Const j ->
            leaders := !leaders |> S.add j |> S.add (i + 1)
        | _ -> ())
      code;
    !leaders
  in
  let rec make_ranges code i leaders ranges =
    if i >= CCVector.length code then ranges
    else
      let next =
        match S.min_elt_opt leaders with
        | Some next -> next
        | None -> CCVector.length code
      in
      let ranges = (i, next - 1) :: ranges in
      make_ranges code next (S.remove next leaders) ranges
  in
  let leaders = identify_leaders code in
  let start = S.min_elt leaders in
  let ranges = make_ranges code start (S.remove start leaders) [] in
  let add_link i j blocks =
    blocks
    |> M.update i
         (Option.map (fun node -> Block.{ node with succ = S.add j node.succ }))
    |> M.update j
         (Option.map (fun node -> Block.{ node with pred = S.add i node.pred }))
  in
  let add_next_link i end_index blocks =
    let next = end_index + 1 in
    if next < CCVector.length code then add_link i next blocks else blocks
  in
  let blocks =
    ranges
    |> List.map (fun (i, j) ->
           let code =
             CCVector.init (j - i + 1) (fun i' -> CCVector.get code (i + i'))
           in
           (i, { code; Block.pred = S.empty; succ = S.empty }))
    |> List.to_seq |> M.of_seq
    |> M.add Block.entry
         { Block.code = CCVector.of_array [||]; pred = S.empty; succ = S.empty }
    |> M.add Block.exit
         { Block.code = CCVector.of_array [||]; pred = S.empty; succ = S.empty }
  in
  let blocks =
    List.fold_left
      (fun blocks (i, end_index) ->
        match CCVector.get code end_index with
        | Goto, Const j, _, _ -> add_link i j blocks
        | (Eq | Ne | Lt | Le | Gt | Ge), _, _, Const j ->
            blocks |> add_link i j |> add_next_link i end_index
        | _ -> add_next_link i end_index blocks)
      blocks ranges
  in
  blocks |> add_link Block.entry 0 |> add_link (fst (List.hd ranges)) Block.exit

type gen_kill_info = {
  gen : S.t CCVector.vector;
  kill : S.t CCVector.vector;
  mutable gen_block : S.t;
  mutable kill_block : S.t;
}

let pp_gen_kill_info fmt info =
  Format.fprintf fmt "{ gen = %s; kill = %s; gen_block = %s; kill_block = %s }"
    ([%show: int list array]
       (Array.map S.elements (CCVector.to_array info.gen)))
    ([%show: int list array]
       (Array.map S.elements (CCVector.to_array info.kill)))
    ([%show: int list] (S.elements info.gen_block))
    ([%show: int list] (S.elements info.kill_block))

let equal_gen_kill_info a b =
  CCVector.(
    List.equal S.equal (to_list a.gen) (to_list b.gen)
    && List.equal S.equal (to_list a.kill) (to_list b.kill))
  && S.equal a.gen_block b.gen_block
  && S.equal a.kill_block b.kill_block

(*
  First pass: generate fresh ints for description id for each instruction,
  set gen(j) to the description id, and add the description id to defs(t).

  Second pass: for each instruction calculate kill using the defs(t) and gen(j).
  Also accumulate the gen_block and kill_block for the whole block.
*)
let gen_kill graph =
  let fresh =
    let i = ref (-1) in
    fun () ->
      incr i;
      !i
  in
  let info =
    M.fold
      (fun i node info ->
        let len = CCVector.length node.Block.code in
        M.add i
          {
            gen = CCVector.init len (fun _ -> S.empty);
            kill = CCVector.init len (fun _ -> S.empty);
            gen_block = S.empty;
            kill_block = S.empty;
          }
          info)
      graph M.empty
  in
  let defs = Hashtbl.create 100 in
  M.iter
    (fun i node ->
      let gen = (M.find i info).gen in
      for j = 0 to CCVector.length node.Block.code - 1 do
        match CCVector.get node.code j with
        | _, _, _, (Temp t | Name t) ->
            let def = fresh () in
            CCVector.set gen j (S.singleton def);
            if Hashtbl.mem defs t then
              Hashtbl.replace defs t (S.add def (Hashtbl.find defs t))
            else Hashtbl.add defs t (S.singleton def)
        | _ -> ()
      done)
    graph;
  M.iter
    (fun i node ->
      let block_info = M.find i info in
      for j = 0 to CCVector.length node.Block.code - 1 do
        match CCVector.get node.code j with
        | _, _, _, (Temp t | Name t) ->
            let gen = CCVector.get block_info.gen j in
            let kill = S.diff (Hashtbl.find defs t) gen in
            CCVector.set block_info.kill j kill;
            block_info.gen_block <-
              S.(union gen (diff block_info.gen_block kill));
            block_info.kill_block <- S.union block_info.kill_block kill
        | _ -> ()
      done)
    graph;
  info

type live_info = { live_in : S.t; live_out : S.t }

let equal_live_info a b =
  S.equal a.live_in b.live_in && S.equal a.live_out b.live_out

let liveness gen_kill graph =
  let rec go info =
    let info' =
      M.fold
        (fun n node info ->
          let live_in =
            List.fold_left
              (fun acc p -> S.union acc (M.find p info).live_out)
              S.empty
              (S.elements node.Block.pred)
          in
          let live_out =
            let gen_kill = M.find n gen_kill in
            S.union gen_kill.gen_block
              (S.diff (M.find n info).live_in gen_kill.kill_block)
          in
          M.add n { live_in; live_out } info)
        graph info
    in
    if not (M.equal equal_live_info info info') then go info' else info'
  in
  go (M.map (fun _ -> { live_in = S.empty; live_out = S.empty }) graph)
