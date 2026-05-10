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

  let is_exit_edge a b = Loop.(loop_header a <> loop_header b)

  let heuristics :
      (float * (Dom.position -> Dom.position -> Dom.position -> bool)) list =
    []

  let calc_branch_prob =
    let prob = Array.make_matrix Dom.size Dom.size 0. in
    for block = 0 to Dom.size do
      let succs = Dom.successors block in
      let n = List.length succs in
      let back_edges =
        List.filter (fun succ -> Dom.dominates succ block) succs
      in
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
    done;
    prob
end
