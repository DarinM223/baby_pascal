include Dataflow_intf

module Make : Maker =
functor
  (G : Graph.S)
  ->
  struct
    module G = G
    type 'a fact = {
      init_info : 'a;
      add_info : 'a -> 'a -> 'a;
      changed : before:'a -> after:'a -> bool;
      get : G.uid -> 'a;
      set : G.uid -> 'a -> unit;
    }
    type 'a answer =
      | Dataflow of 'a
      | Rewrite of G.graph

    let update (fact : 'a fact) (changed : bool ref) (uid : G.uid) (a : 'a) =
      let old_a = fact.get uid in
      let new_a = fact.add_info a old_a in
      if fact.changed ~before:old_a ~after:new_a then begin
        fact.set uid new_a;
        if uid <> G.entry_uid then changed := true
      end

    let run fact changed entry_fact f blocks =
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

    let without_changing_entry (fact : 'a fact) (f : unit -> 'b) : 'b * 'a =
      let restore =
        try
          let old_fact = fact.get G.entry_uid in
          fun () -> fact.set G.entry_uid old_fact
        with Not_found -> fun () -> ()
      in
      let result = f () in
      let entry_info = fact.get G.entry_uid in
      restore ();
      (result, entry_info)

    module BackwardAnalysis = struct
      type 'a functions = {
        first_in : 'a -> G.first -> 'a;
        middle_in : 'a -> G.middle -> 'a;
        last_in : G.last -> 'a;
      }
      type 'a t = 'a fact * 'a functions

      let run (fact, analysis) graph =
        let changed = ref false in
        let set_block_fact block =
          let head, last = G.(goto_end (unzip block)) in
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

    module BackwardPass = struct
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

      let rec solve_graph ((fact, _) as pass) graph exit_fact =
        snd
        @@ without_changing_entry fact
        @@ fun () -> general_backward (with_exit pass exit_fact) graph

      and general_backward ((fact, pass_fns) as pass) graph =
        let changed = ref false in
        let set_block_fact b =
          let rec head_in head out =
            match head with
            | G.Head (h, m) ->
              head_in h
                (match pass_fns.middle_in out m with
                | Dataflow a -> a
                | Rewrite g -> solve_graph pass g out)
            | G.First f ->
              (match pass_fns.first_in out f with
              | Dataflow a -> a
              | Rewrite g -> solve_graph pass g out)
          in
          let head, last = G.(goto_end (unzip b)) in
          let block_in =
            head_in head
              (match pass_fns.last_in last with
              | Dataflow a -> a
              | Rewrite g -> solve_graph pass g fact.init_info)
          in
          update fact changed (G.id b) block_in
        in
        let blocks = List.rev (G.reverse_postorder_dfs graph) in
        run fact changed fact.init_info set_block_fact blocks

      let rec solve_and_rewrite pass graph exit_fact changed =
        let entry_info = solve_graph pass graph exit_fact in
        let result =
          backward_rewrite (with_exit pass exit_fact) graph changed
        in
        (entry_info, result)

      and backward_rewrite ((fact, pass_fns) as pass) graph changed =
        let rec rewrite_blocks changed rewritten = function
          | [] -> (rewritten, changed)
          | b :: bs ->
            let rec propagate head a t rewritten changed =
              match head with
              | G.Head (h, m) -> begin
                match pass_fns.middle_in a m with
                | Dataflow a -> propagate h a (G.Tail (m, t)) rewritten changed
                | Rewrite g ->
                  let a, (g, _) = solve_and_rewrite pass g a changed in
                  let t, g = G.splice_tail g t in
                  let rewritten = G.Blocks.union g rewritten in
                  propagate h a t rewritten true
              end
              | G.First f -> begin
                match pass_fns.first_in a f with
                | Dataflow _ ->
                  rewrite_blocks changed (G.Blocks.insert (f, t) rewritten) bs
                | Rewrite _ ->
                  failwith "rewriting a label in backwards dataflow"
              end
            in
            let head, last = G.(goto_end (unzip b)) in
            begin match pass_fns.last_in last with
            | Dataflow a -> propagate head a (G.Last last) rewritten changed
            | Rewrite g ->
              let a, (g, _) = solve_and_rewrite pass g fact.init_info changed in
              let t, g = G.remove_entry g in
              let rewritten = G.Blocks.union g rewritten in
              propagate head a t rewritten true
            end
        in
        rewrite_blocks changed G.empty
          (List.rev (G.reverse_postorder_dfs graph))
    end
  end
