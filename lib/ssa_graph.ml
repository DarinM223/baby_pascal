open Code
open Cfg

type edge =
  | Phi of Block.phi
  | Quad of quad
[@@deriving show, eq]

(*
  Builds a demand driven use-def SSA graph from the SSA control-flow graph.
  Useful for things like induction variable detection and operator strength reduction.
*)
let use_def_chains graph =
  let table = Hashtbl.create 1000 in
  M.iter
    (fun _ node ->
      CCVector.iter
        (fun phi -> Hashtbl.add table phi.Block.r (Phi phi))
        node.Block.phis;
      CCVector.iter
        (function
          | { r = Name _ | Temp _; _ } as quad ->
            Hashtbl.add table quad.r (Quad quad)
          | _ -> ())
        node.code)
    graph;
  table

(*
  Builds a def-use SSA graph from the SSA control-flow graph.
  Useful for instruction selection. Every name has multiple edges,
  so you would use Hashtbl.find_all to get all of them.
*)
let def_use_chains graph =
  let table = Hashtbl.create 1000 in
  M.iter
    (fun _ node ->
      CCVector.iter
        (fun phi ->
          List.iter (fun addr -> Hashtbl.add table addr (Phi phi)) phi.ins)
        node.Block.phis;
      CCVector.iter
        (fun quad ->
          (match quad.a with
          | Name _ | Temp _ -> Hashtbl.add table quad.a (Quad quad)
          | _ -> ());
          match quad.b with
          | Name _ | Temp _ -> Hashtbl.add table quad.b (Quad quad)
          | _ -> ())
        node.code)
    graph;
  table

module Worklist = Set.Make (Addr)

(* Get all variables in the program *)
let variables graph =
  let vars = ref Worklist.empty in
  let add_var = function
    | Addr.(Name _ | Temp _) as addr -> vars := Worklist.add addr !vars
    | _ -> ()
  in
  M.iter
    (fun _ node ->
      CCVector.iter
        (fun phi ->
          List.iter (fun addr -> add_var addr) phi.Block.ins;
          add_var phi.r)
        node.Block.phis;
      CCVector.iter
        (fun quad ->
          add_var quad.a;
          add_var quad.b;
          add_var quad.r)
        node.code)
    graph;
  !vars
