(** Loop branch heuristic: Predict as taken an edge back to a loop's head.
    Predict as not taken an edge exiting a loop. *)
let lbh_prob = 0.88

(** Call heuristic: Predict a successor that contains a call and does not
    post-dominate will not be taken. *)
let ch_prob = 0.78

(** Opcode heuristic: Predict that a comparison of an integer for less than
    zero, less than or equal to zero, or equal to a constant, will fail. *)
let oh_prob = 0.84

(** Loop exit heuristic: Predict that a comparison in a loop in which no
    successor is a loop head will not exit the loop. *)
let leh_prob = 0.8

let not_taken prob = 1. -. prob

module Make
    (G : Graph.S)
    (Loop :
      Loopnesting.S
        with type Dom.label = G.label
         and type Dom.graph = G.graph
         and type Dom.position = int
         and type Dom.uid = G.uid) =
struct
  module Dom = Loop.Dom

  let calls_exit = Array.init Dom.size (fun _block -> false)

  let is_back_edge a b = Dom.dominates b a
  let is_exit_edge a b = Loop.(loop_header a <> loop_header b)

  let heuristics :
      (float * (Dom.position -> Dom.position -> Dom.position -> bool)) list =
    []

  let prob = Array.make_matrix Dom.size Dom.size 0.
  let bfreq = Array.make Dom.size 0.
  let freq = Array.make_matrix Dom.size Dom.size 0.

  let calc_branch_prob () =
    for block = 0 to Dom.size do
      let succs = Dom.successors block in
      let n = List.length succs in
      let back_edges = List.filter (is_back_edge block) succs in
      let m = List.length back_edges in
      let exit_edges = List.filter (is_exit_edge block) succs in
      if n <> 0 then ()
      else if calls_exit.(block) then begin
        List.iter (fun succ -> prob.(block).(succ) <- 0.) succs
      end
      else if m > 0 && m < n then begin
        List.iter
          (fun succ -> prob.(block).(succ) <- lbh_prob /. float_of_int m)
          back_edges;
        List.iter
          (fun succ ->
            prob.(block).(succ) <- not_taken lbh_prob /. float_of_int (n - m))
          exit_edges
      end
      else if m > 0 && n <> 2 then
        List.iter
          (fun succ -> prob.(block).(succ) <- 1. /. float_of_int n)
          succs
      else begin
        let s1, s2 =
          match succs with
          | [ s1; s2 ] -> (s1, s2)
          | _ -> failwith "expected only two successors"
        in
        prob.(block).(s1) <- 0.5;
        prob.(block).(s2) <- 0.5;
        let go_heuristic h =
          let d =
            (prob.(block).(s1) *. h) +. (prob.(block).(s2) *. not_taken h)
          in
          prob.(block).(s1) <- prob.(block).(s1) *. h /. d;
          prob.(block).(s2) <- prob.(block).(s2) *. not_taken h /. d
        in
        List.iter
          (fun (prob, f) -> if f block s1 s2 then go_heuristic prob)
          heuristics
      end
    done

  module IntHashtbl = Hashtbl.Make (Int)

  let inner_to_outer_loops : Dom.position array =
    let visited = IntHashtbl.create Dom.size in
    let arr = Dynarray.create () in
    let rec go node =
      let loop_nodes = Iarray.get Loop.loop_nodes node in
      Loop.PositionSet.iter
        (fun nested ->
          if
            (not (IntHashtbl.mem visited nested))
            && Loop.PositionSet.mem nested Loop.loop_headers
          then go nested)
        loop_nodes;
      Dynarray.add_last arr node;
      IntHashtbl.replace visited node ()
    in
    let root = Dom.position_of_uid G.entry_uid in
    go root;
    Dynarray.to_array arr

  let compute_freq () =
    let not_visited : unit IntHashtbl.t = IntHashtbl.create Dom.size in
    let back_edge_prob = Array.map Array.copy prob in
    let exception Return in
    let rec propagate_freq block head =
      try
        if IntHashtbl.mem not_visited block then begin
          if block = head then bfreq.(block) <- 1.
          else begin
            List.iter
              (fun pred ->
                if
                  IntHashtbl.mem not_visited pred
                  && not (is_back_edge pred block)
                then raise Return)
              (Dom.predecessors block);
            bfreq.(block) <- 0.;
            let cyclic_probability = ref 0. in
            let go_pred pred =
              if
                is_back_edge pred block
                && Loop.PositionSet.mem block Loop.loop_headers
              then
                cyclic_probability :=
                  !cyclic_probability +. back_edge_prob.(pred).(block)
              else bfreq.(block) <- bfreq.(block) +. freq.(pred).(block)
            in
            List.iter go_pred (Dom.predecessors block);
            if !cyclic_probability > 1. -. epsilon_float then
              cyclic_probability := 1. -. epsilon_float;
            bfreq.(block) <- bfreq.(block) /. (1. -. !cyclic_probability)
          end;
          IntHashtbl.remove not_visited block;
          let go_succ succ =
            freq.(block).(succ) <- prob.(block).(succ) *. bfreq.(block);
            if succ = head then
              back_edge_prob.(block).(succ) <-
                prob.(block).(succ) *. bfreq.(block)
          in
          List.iter go_succ (Dom.successors block);
          List.iter
            (fun succ ->
              if not (is_back_edge block succ) then propagate_freq succ head)
            (Dom.successors block)
        end
      with Return -> ()
    in
    for i = 0 to Array.length inner_to_outer_loops - 1 do
      let head = inner_to_outer_loops.(i) in
      IntHashtbl.clear not_visited;
      (* mark all blocks reachable from head as not visited *)
      let head_uid = G.idd (Dom.label_of_position head) in
      List.iter
        (fun block ->
          let pos = Dom.position_of_label (G.block_label block) in
          IntHashtbl.replace not_visited pos ())
        (G.reverse_postorder_dfs_from head_uid Dom.graph);
      propagate_freq head head
    done

  let () = calc_branch_prob ()
  let () = compute_freq ()
end
