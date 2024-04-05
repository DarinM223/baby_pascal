let has_side_effects _ = false

let deadcode def_use graph =
  let module Worklist = Ssa_graph.Worklist in
  let worklist = ref (Ssa_graph.variables graph) in
  while not (Worklist.is_empty !worklist) do
    let stmt = Worklist.min_elt !worklist in
    worklist := Worklist.remove stmt !worklist;
    match Hashtbl.find_all def_use stmt with
    | [] when not (has_side_effects stmt) -> failwith ""
    | _ -> ()
  done;
  failwith ""
