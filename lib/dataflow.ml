module Make (G : Graph.S) = struct
  type 'a fact = {
    init_info : 'a;
    add_info : 'a -> 'a -> 'a;
    changed : before:'a -> after:'a -> bool;
    get : G.uid -> 'a;
    set : G.uid -> 'a -> unit;
  }

  let update (fact : 'a fact) (changed : bool ref) (uid : G.uid) (a : 'a) =
    let old_a = fact.get uid in
    let new_a = fact.add_info a old_a in
    if fact.changed ~before:old_a ~after:new_a then begin
      fact.set uid new_a;
      if uid <> G.entry_uid then changed := true
    end

  let run (fact : 'a fact) (changed : bool ref) (entry_fact : 'a)
      (f : G.block -> unit) (blocks : G.block list) : int =
    let rec iterate n =
      changed := false;
      List.iter f blocks;
      if !changed then
        if n < 1000 then iterate (n + 1) else failwith "didn't converge"
      else n
    in
    List.iter (fun block -> fact.set (G.id block) fact.init_info) blocks;
    fact.set G.entry_uid entry_fact;
    iterate 1

  module Analysis = struct
    type 'a functions = {
      first_in : 'a -> G.first -> 'a;
      middle_in : 'a -> G.middle -> 'a;
      last_in : G.last -> 'a;
    }
    type 'a t = 'a fact * 'a functions

    let run_analysis (fact, analysis) graph =
      let changed = ref false in
      let set_block_fact block =
        let head, last = G.goto_end (G.unzip block) in
        let rec head_in head out =
          match head with
          | G.Head (h, m) -> head_in h (analysis.middle_in out m)
          | G.First f -> analysis.first_in out f
        in
        let block_in = head_in head (analysis.last_in last) in
        update fact changed (G.id block) block_in
      in
      let blocks = List.rev (G.reverse_postorder_dfs graph) in
      run fact changed fact.init_info set_block_fact blocks
  end

  module Pass = struct
    type 'a answer =
      | Dataflow of 'a
      | Rewrite of G.graph
    type 'a functions = {
      first_in : 'a -> G.first -> 'a answer;
      middle_in : 'a -> G.middle -> 'a answer;
      last_in : G.last -> 'a answer;
    }
    type 'a t = 'a fact * 'a functions

    let with_exit ((fact, pass_fns) : 'a t) (exit_fact : 'a) : 'a t =
      let last_in = function
        | G.Exit -> Dataflow exit_fact
        | l -> pass_fns.last_in l
      in
      (fact, { pass_fns with last_in })
  end
end
