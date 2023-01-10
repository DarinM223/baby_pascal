open Cfg
open Code

let calc_a_orig gen_kill instr_of_def n =
  (M.find n gen_kill).gen_block
  |> S.filter_map (fun def ->
         match instr_of_def def with
         | _, _, _, Name (t, _) -> Some t
         | _ -> None)
  |> S.to_seq |> List.of_seq

let insert_phis test df a_orig v g =
  let defsites = Hashtbl.create (S.cardinal v) in
  M.iter (fun n _ -> List.iter (fun a -> Hashtbl.add defsites a n) (a_orig n)) g;
  let a_phi = Hashtbl.create (S.cardinal v) in
  S.iter
    (fun a ->
      let a' = name a in
      let w = ref (S.of_list (Hashtbl.find_all defsites a)) in
      while not (S.is_empty !w) do
        let n = S.min_elt !w in
        w := S.remove n !w;
        List.iter
          (fun y ->
            if (not (List.mem y (Hashtbl.find_all a_phi a))) && test y a then (
              let node = M.find y g in
              let phi = List.init (S.cardinal node.Block.pred) (fun _ -> a') in
              CCVector.push node.phis (a', phi);
              Hashtbl.add a_phi a y;
              if not (List.mem a (a_orig y)) then w := S.add y !w))
          (df n)
      done)
    v

let insert_phis_minimal = insert_phis (fun _ _ -> true)

let insert_phis_pruned live_map =
  insert_phis (fun y a -> S.mem a (M.find y live_map).live_in)

let find_index a l =
  let exception Found of int in
  try
    List.iteri (fun i e -> if e = a then raise (Found i)) l;
    raise Not_found
  with Found i -> i

let replace_in_list index new_elem =
  let[@tail_mod_cons] rec go i = function
    | x :: xs -> if i = index then new_elem :: xs else x :: go (i + 1) xs
    | [] -> raise Not_found
  in
  go 0

let rename v g =
  let count = Hashtbl.create (S.cardinal v) in
  let stack = Hashtbl.create (S.cardinal v) in
  S.iter
    (fun a ->
      Hashtbl.add count a 0;
      Hashtbl.add stack a 0)
    v;
  let replace_def defs = function
    | Name (a, _) ->
        defs := S.add a !defs;
        let i = Hashtbl.find count a + 1 in
        Hashtbl.replace count a i;
        Hashtbl.add stack a i;
        Name (a, i)
    | r -> r
  in
  let rename_instr defs (op, a, b, r) =
    let r = replace_def defs r in
    match (a, b) with
    | Name (n1, _), Name (n2, _) ->
        let i1 = Hashtbl.find stack n1 in
        let i2 = Hashtbl.find stack n2 in
        (op, Name (n1, i1), Name (n2, i2), r)
    | Name (n, _), t ->
        let i = Hashtbl.find stack n in
        (op, Name (n, i), t, r)
    | t, Name (n, _) ->
        let i = Hashtbl.find stack n in
        (op, t, Name (n, i), r)
    | _ -> (op, a, b, r)
  in
  let traversed = Hashtbl.create (M.cardinal g) in
  let rec rename_block n =
    if not (Hashtbl.mem traversed n) then (
      Hashtbl.add traversed n ();
      (* Remember defs as they are replaced so you can pop them later. *)
      let defs = ref S.empty in
      let node = M.find n g in
      CCVector.iteri
        (fun s (a, rest) ->
          CCVector.set node.Block.phis s (replace_def defs a, rest))
        node.phis;
      CCVector.iteri
        (fun s instr -> CCVector.set node.code s (rename_instr defs instr))
        node.code;
      S.iter
        (fun y ->
          let succ_node = M.find y g in
          let j = succ_node.pred |> S.elements |> find_index n in
          CCVector.map_in_place
            (fun (r, s) ->
              match List.nth_opt s j with
              | Some (Name (a, _)) ->
                  let i = Hashtbl.find stack a in
                  (r, replace_in_list j (Name (a, i)) s)
              | _ -> (r, s))
            succ_node.phis)
        node.succ;
      S.iter rename_block (S.union node.pred node.succ);
      S.iter (Hashtbl.remove stack) !defs)
  in
  rename_block Block.entry
