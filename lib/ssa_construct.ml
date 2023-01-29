open Cfg
open Code

let calc_a_orig g =
  let a_orig = Hashtbl.create (M.cardinal g) in
  M.iter
    (fun n node ->
      let result =
        CCVector.fold
          (fun l -> function { r = Name (t, _); _ } -> t :: l | _ -> l)
          [] node.Block.code
      in
      Hashtbl.add a_orig n result)
    g;
  Hashtbl.find a_orig

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
              CCVector.push node.phis { r = a'; ins = phi };
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
  let rename_instr defs quad =
    quad.r <- replace_def defs quad.r;
    (match quad.a with
    | Name (n, _) -> quad.a <- Name (n, Hashtbl.find stack n)
    | _ -> ());
    match quad.b with
    | Name (n, _) -> quad.b <- Name (n, Hashtbl.find stack n)
    | _ -> ()
  in
  let traversed = Hashtbl.create (M.cardinal g) in
  let rec rename_block n =
    if not (Hashtbl.mem traversed n) then (
      Hashtbl.add traversed n ();
      (* Remember defs as they are replaced so you can pop them later. *)
      let defs = ref S.empty in
      let node = M.find n g in
      CCVector.iter
        (fun phi -> phi.Block.r <- replace_def defs phi.Block.r)
        node.Block.phis;
      CCVector.iter (rename_instr defs) node.code;
      S.iter
        (fun y ->
          let succ_node = M.find y g in
          let j = succ_node.pred |> S.elements |> find_index n in
          CCVector.iter
            (fun phi ->
              match List.nth_opt phi.Block.ins j with
              | Some (Name (a, _)) ->
                  let i = Hashtbl.find stack a in
                  phi.ins <- replace_in_list j (Name (a, i)) phi.ins
              | _ -> ())
            succ_node.phis)
        node.succ;
      S.iter rename_block (S.union node.pred node.succ);
      S.iter (Hashtbl.remove stack) !defs)
  in
  rename_block Block.entry
