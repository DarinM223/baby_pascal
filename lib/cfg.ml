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
  blocks

type set = bytes

(*
  Stores gen/kill sets for the whole block and for each statement
  in the block (in order to recover the dataflow information
  of an individual statement).
*)
type gen_kill_info = {
  gen : set array;
  kill : set array;
  gen_block : set;
  kill_block : set;
}

let gen_kill : Block.t -> gen_kill_info = fun _ -> failwith ""
