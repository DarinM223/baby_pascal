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
      skip_block : G.uid -> bool;
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
        List.iter (fun b -> if not (fact.skip_block (G.id b)) then f b) blocks;
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

    let skipping_entry (fact, fns) =
      ( {
          fact with
          skip_block = (fun uid -> uid = G.entry_uid || fact.skip_block uid);
        },
        fns )

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
              | Rewrite g -> solve_graph (skipping_entry pass) g out)
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
                | Rewrite g ->
                  let _, (g, _) =
                    solve_and_rewrite (skipping_entry pass) g a changed
                  in
                  begin match f with
                  | G.Entry ->
                    let t, g = G.splice_tail g t in
                    let rewritten = G.Blocks.union g rewritten in
                    rewrite_blocks changed
                      (G.Blocks.insert (G.Entry, t) rewritten)
                      bs
                  | G.Label ((uid, _), _) ->
                    let f =
                      match G.focus uid g with
                      | (First f, _), _ -> f
                      | _ -> failwith "block doesn't have first, cannot happen"
                    in
                    let t, g =
                      G.(splice_tail ~entry:uid (snd (remove_entry g)) t)
                    in
                    let rewritten = G.Blocks.union g rewritten in
                    rewrite_blocks changed (G.Blocks.insert (f, t) rewritten) bs
                  end
              end
            in
            if fact.skip_block (G.id b) then
              rewrite_blocks changed (G.Blocks.insert b rewritten) bs
            else
              let head, last = G.(goto_end (unzip b)) in
              begin match pass_fns.last_in last with
              | Dataflow a -> propagate head a (G.Last last) rewritten changed
              | Rewrite g ->
                let a, (g, _) =
                  solve_and_rewrite pass g fact.init_info changed
                in
                let t, g = G.remove_entry g in
                let rewritten = G.Blocks.union g rewritten in
                propagate head a t rewritten true
              end
        in
        rewrite_blocks changed G.empty
          (List.rev (G.reverse_postorder_dfs graph))

      let solve_and_rewrite pass graph entry =
        solve_and_rewrite pass graph entry false
    end

    module ForwardAnalysis = struct
      type 'a functions = {
        first_out : G.first -> 'a;
        middle_out : 'a -> G.middle -> 'a;
        last_outs : 'a -> G.last -> (G.uid -> 'a -> unit) -> unit;
      }
      type 'a t = 'a fact * 'a functions

      let run ~entry_fact (fact, analysis) graph =
        let changed = ref false in
        let set_successor_facts (first, tail) =
          let update = update fact changed in
          let rec forward in' = function
            | G.Tail (m, t) -> forward (analysis.middle_out in' m) t
            | G.Last l -> analysis.last_outs in' l update
          in
          forward (analysis.first_out first) tail
        in
        let blocks = G.reverse_postorder_dfs graph in
        run fact changed entry_fact set_successor_facts blocks
    end

    module ForwardPass = struct
      type 'a functions = {
        first_out : G.first -> 'a answer;
        middle_out : 'a -> G.middle -> 'a answer;
        last_outs : 'a -> G.last -> ((G.uid -> 'a -> unit) -> unit) answer;
      }
      type 'a t = 'a fact * 'a functions

      let with_entry ((fact, pass_fns) : 'a t) (entry_fact : 'a) : 'a t =
        let first_out = function
          | G.Entry -> Dataflow entry_fact
          | f -> pass_fns.first_out f
        in
        (fact, { pass_fns with first_out })

      let with_exit (fact, pass_fns) exit_fact_ref =
        let last_outs in' = function
          | G.Exit -> Dataflow (fun _ -> exit_fact_ref := in')
          | l -> pass_fns.last_outs in' l
        in
        (fact, { pass_fns with last_outs })

      let rec solve_graph ((fact, _) as pass) graph entry_fact =
        let exit_fact_ref = ref fact.init_info in
        let pass = with_entry (with_exit pass exit_fact_ref) entry_fact in
        let _ = general_forward pass graph in
        !exit_fact_ref

      and general_forward ((fact, pass_fns) as pass) graph =
        let changed = ref false in
        let update = update fact changed in
        let set_successor_facts (first, tail) =
          let rec set_tail_facts in' = function
            | G.Tail (m, t) -> begin
              match pass_fns.middle_out in' m with
              | Dataflow a -> set_tail_facts a t
              | Rewrite g -> set_tail_facts (solve_graph pass g in') t
            end
            | G.Last l -> begin
              match pass_fns.last_outs in' l with
              | Dataflow setter -> setter update
              | Rewrite g -> ignore (solve_graph pass g in')
            end
          in
          let in' =
            match pass_fns.first_out first with
            | Dataflow a -> a
            | Rewrite g -> solve_graph pass g fact.init_info
          in
          set_tail_facts in' tail
        in
        let blocks = G.reverse_postorder_dfs graph in
        run fact changed fact.init_info set_successor_facts blocks

      let check_property_match (fact : 'a fact) uid a =
        let a' = fact.get uid in
        let a = fact.add_info a a' in
        if fact.changed ~before:a ~after:a' || fact.changed ~before:a' ~after:a
        then
          failwith
          @@ Format.sprintf
               "property at label %s changed after reaching fixed point"
          @@ G.show_uid uid

      let rec solve_and_rewrite ((fact, _) as pass) graph entry_fact changed =
        let _ = solve_graph pass graph entry_fact in
        let exit_ref = ref fact.init_info in
        let pass = with_entry (with_exit pass exit_ref) entry_fact in
        let result = forward_rewrite pass graph changed in
        (!exit_ref, result)

      and forward_rewrite ((fact, pass_fns) as pass) graph changed =
        let rec rewrite_blocks changed rewritten = function
          | [] -> (rewritten, changed)
          | b :: bs ->
            let rec propagate h a tail rewritten changed =
              match tail with
              | G.Tail (m, t) -> begin
                match pass_fns.middle_out a m with
                | Dataflow a -> propagate (G.Head (h, m)) a t rewritten changed
                | Rewrite g ->
                  let a, (g, _) = solve_and_rewrite pass g a changed in
                  let g, h = G.splice_head h g in
                  let rewritten = G.Blocks.union g rewritten in
                  propagate h a t rewritten true
              end
              | G.Last l -> begin
                match pass_fns.last_outs a l with
                | Dataflow set ->
                  set (check_property_match fact);
                  rewrite_blocks changed
                    G.(Blocks.insert (zip (h, Last l)) rewritten)
                    bs
                | Rewrite g ->
                  rewrite_blocks true
                    (G.Blocks.union (G.splice_head_only h g) rewritten)
                    bs
              end
            in
            if fact.skip_block (G.id b) then
              rewrite_blocks changed (G.Blocks.insert b rewritten) bs
            else
              let first, tail = b in
              begin match pass_fns.first_out first with
              | Dataflow a -> propagate (G.First first) a tail rewritten changed
              | Rewrite g ->
                let a, (g, _) =
                  solve_and_rewrite (skipping_entry pass) g fact.init_info
                    changed
                in
                begin match first with
                | G.Entry ->
                  let g, h = G.splice_head (G.First G.Entry) g in
                  let rewritten = G.Blocks.union g rewritten in
                  propagate h a tail rewritten true
                | G.Label ((uid, _), _) ->
                  let f =
                    match G.focus uid g with
                    | (First f, _), _ -> f
                    | _ -> failwith "block doesn't have first, cannot happen"
                  in
                  let g, h =
                    G.(splice_head ~entry:uid (First f) (snd (remove_entry g)))
                  in
                  let rewritten = G.Blocks.union g rewritten in
                  propagate h a tail rewritten true
                end
              end
        in
        rewrite_blocks changed G.empty (G.reverse_postorder_dfs graph)

      let solve_and_rewrite pass graph entry_fact =
        solve_and_rewrite pass graph entry_fact false
    end
  end
