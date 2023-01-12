open Code

module S = struct
  include Set.Make (Int)

  let pp fmt s =
    Format.fprintf fmt "S.of_list %s" ([%show: int list] (elements s))
end

module M = Map.Make (Int)

module Block = struct
  type phi = addr * addr list [@@deriving show, eq]

  type t = {
    phis : phi CCVector.vector;
    code : quad CCVector.vector;
    pred : S.t;
    succ : S.t;
  }

  let pp fmt block =
    Format.fprintf fmt
      "{ phis = CCVector.of_array %s; code = CCVector.of_array %s; pred = %a; \
       succ = %a }"
      ([%show: phi array] (CCVector.to_array block.phis))
      ([%show: quad array] (CCVector.to_array block.code))
      S.pp block.pred S.pp block.succ

  let equal a b =
    CCVector.(
      to_array a.phis = to_array b.phis && to_array a.code = to_array b.code)
    && S.equal a.pred b.pred && S.equal a.succ b.succ

  let create code =
    { phis = CCVector.create (); code; pred = S.empty; succ = S.empty }

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
           (i, Block.create code))
    |> List.to_seq |> M.of_seq
    |> M.add Block.entry (Block.create (CCVector.create ()))
    |> M.add Block.exit (Block.create (CCVector.create ()))
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
  Format.fprintf fmt
    "{ gen = CCVector.of_array %s; kill = CCVector.of_array %s; gen_block = \
     %a; kill_block = %a }"
    ([%show: S.t array] (CCVector.to_array info.gen))
    ([%show: S.t array] (CCVector.to_array info.kill))
    S.pp info.gen_block S.pp info.kill_block

let equal_gen_kill_info a b =
  CCVector.(
    List.equal S.equal (to_list a.gen) (to_list b.gen)
    && List.equal S.equal (to_list a.kill) (to_list b.kill))
  && S.equal a.gen_block b.gen_block
  && S.equal a.kill_block b.kill_block

let gen_kill graph =
  let info_map =
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
  let get_name = function Name (n, _) -> Some n | _ -> None in
  M.iter
    (fun i node ->
      let info = M.find i info_map in
      for j = CCVector.length node.Block.code - 1 downto 0 do
        let _, a, b, c = CCVector.get node.code j in
        let gen = [ a; b ] |> List.filter_map get_name |> S.of_list in
        let kill = Option.fold ~none:S.empty ~some:S.singleton (get_name c) in
        CCVector.set info.gen j gen;
        CCVector.set info.kill j kill;
        info.gen_block <- S.union info.gen_block gen;
        info.kill_block <- S.(union kill (diff info.kill_block gen))
      done)
    graph;
  info_map

type live_info = { live_in : S.t; live_out : S.t }

let pp_live_info fmt info =
  Format.fprintf fmt "{ live_in = %a; live_out = %a }" S.pp info.live_in S.pp
    info.live_out

let equal_live_info a b =
  S.equal a.live_in b.live_in && S.equal a.live_out b.live_out

let liveness gen_kill graph =
  let rec go info =
    let info' =
      M.fold
        (fun n node info' ->
          let live_in =
            let gen_kill = M.find n gen_kill in
            S.union gen_kill.gen_block
              (S.diff (M.find n info).live_out gen_kill.kill_block)
          in
          let live_out =
            List.fold_left
              (fun acc s -> S.union acc (M.find s info).live_in)
              S.empty
              (S.elements node.Block.succ)
          in
          M.add n { live_in; live_out } info')
        graph M.empty
    in
    if not (M.equal equal_live_info info info') then go info' else info'
  in
  go (M.map (fun _ -> { live_in = S.empty; live_out = S.empty }) graph)
