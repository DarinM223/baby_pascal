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

(** Return heuristic: Predict a successor that contains a return will not be
    taken. *)
let rh_prob = 0.72

(** Loop Header heuristic: Predict a successor that is a loop header or a loop
    pre-header and does not post-dominate will be taken. *)
let lhh_prob = 0.75

let not_taken prob = 1. -. prob

module type Requirements = sig
  module Target : Graph.Target
  val instr_name : Target.instr -> string
  val imm : Target.operand -> int option
  val label : Target.operand -> Target.label option
  val uses : Target.instr -> Target.operands
  val call : string
  val ret : string
  val cmp : string
end

module Make
    (G :
      Graph.S
        with type label = int * string
         and type Target.label = int * string)
    (Loop :
      Loopnesting.S
        with type Dom.label = G.label
         and type Dom.graph = G.graph
         and type Dom.position = int
         and type Dom.uid = G.uid)
    (Requirements : Requirements with module Target = G.Target) =
struct
  module Dom = Loop.Dom

  let calls_exit = Array.init Dom.size (fun _block -> false)

  let is_back_edge a b = Dom.dominates b a
  let is_exit_edge a b = Loop.(loop_header a <> loop_header b)

  let contains_instr (f : G.Target.instr -> bool) (pos : Dom.position) : bool =
    let uid = G.idd (Dom.label_of_position pos) in
    let (_, tail), _ = G.focus uid Dom.graph in
    let rec go_tail (tail : G.tail) =
      match tail with
      | G.Last _ -> false
      | G.Tail (G.Instruction i, tail) -> f i || go_tail tail
    in
    go_tail tail
  let contains_instr_name name =
    contains_instr (fun i -> Requirements.instr_name i = name)
  let cmp_zero_or_constant name not_taken_succ ops =
    let lt = Requirements.cmp ^ " " ^ "LT" in
    let le = Requirements.cmp ^ " " ^ "LE" in
    let eq = Requirements.cmp ^ " " ^ "EQ" in
    match ops with
    | [ _; b; _; l2 ] ->
      Requirements.label l2 = Some not_taken_succ
      && begin match Requirements.imm b with
      | Some 0 when name = lt || name = le || name = eq -> true
      | Some _ when name = eq -> true
      | _ -> false
      end
    | _ -> false
  let contains_opcode not_taken_succ =
    contains_instr (fun i ->
        let name = Requirements.instr_name i in
        String.length name >= 3
        && String.sub name 0 3 = Requirements.cmp
        && cmp_zero_or_constant name not_taken_succ (Requirements.uses i))

  (* Probabilities that s1 will be taken *)
  let heuristics :
      (float * (Dom.position -> Dom.position -> Dom.position -> bool)) list =
    [
      ( ch_prob,
        fun n _ s2 ->
          contains_instr_name Requirements.call s2 && not (Dom.dominates s2 n)
      );
      ( not_taken ch_prob,
        fun n s1 _ ->
          contains_instr_name Requirements.call s1 && not (Dom.dominates s1 n)
      );
      (rh_prob, fun _ _ s2 -> contains_instr_name Requirements.ret s2);
      (not_taken rh_prob, fun _ s1 _ -> contains_instr_name Requirements.ret s1);
      ( oh_prob,
        fun n _ s2 ->
          let l = Dom.label_of_position s2 in
          Option.is_some l && contains_opcode (Option.get l) n );
      ( not_taken oh_prob,
        fun n s1 _ ->
          let l = Dom.label_of_position s1 in
          Option.is_some l && contains_opcode (Option.get l) n );
    ]

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
