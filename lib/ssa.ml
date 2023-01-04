open Cfg
open Code

let insert_phis df a_orig v g =
  let defsites = Hashtbl.create (S.cardinal v) in
  M.iter
    (fun n _ ->
      List.iter
        (fun a -> Hashtbl.(replace defsites a (S.add n (find defsites a))))
        (a_orig n))
    g;
  let a_phi = Hashtbl.create (S.cardinal v) in
  S.iter
    (fun a ->
      let w = ref (Hashtbl.find defsites a) in
      while not (S.is_empty !w) do
        let n = S.min_elt !w in
        w := S.remove n !w;
        List.iter
          (fun y ->
            if not (List.mem y (Hashtbl.find_all a_phi a)) then (
              let node = M.find y g in
              let phi = List.init (S.cardinal node.Block.pred) (fun _ -> a) in
              CCVector.push node.phis (a, phi);
              Hashtbl.add a_phi a y;
              if not (List.mem a (a_orig y)) then w := S.add y !w))
          (df n)
      done)
    v

let find_index a l =
  let exception Found of int in
  try
    List.iteri (fun i e -> if e = a then raise (Found i)) l;
    raise Not_found
  with Found i -> i

let replace_in_list index new_elem =
  let[@tail_mod_cons] rec go i = function
    | x :: xs -> if i = index then new_elem :: xs else x :: go (i + 1) xs
    | [] -> []
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
  let replace a i = get_sym (get_name a ^ string_of_int i) in
  let replace_def defs a =
    defs := S.add a !defs;
    let i = Hashtbl.find count a + 1 in
    Hashtbl.replace count a i;
    Hashtbl.add stack a i;
    replace a i
  in
  let rename_instr defs (op, a, b, r) =
    let r = match r with Name a -> Name (replace_def defs a) | _ -> r in
    match (a, b) with
    | Name n1, Name n2 ->
        let i1 = Hashtbl.find stack n1 in
        let i2 = Hashtbl.find stack n2 in
        (op, Name (replace n1 i1), Name (replace n2 i2), r)
    | Name n, t ->
        let i = Hashtbl.find stack n in
        (op, Name (replace n i), t, r)
    | t, Name n ->
        let i = Hashtbl.find stack n in
        (op, t, Name (replace n i), r)
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
              let a = List.nth s j in
              let i = Hashtbl.find stack a in
              (r, replace_in_list j (replace a i) s))
            succ_node.phis)
        node.succ;
      S.iter rename_block (S.union node.pred node.succ);
      S.iter (Hashtbl.remove stack) !defs)
  in
  rename_block Block.entry