module IntHashtbl = Hashtbl.Make (Int)

let calc_live (_g : Normalize.Cfg.graph) =
  let open Normalize in
  let gen_kill = IntHashtbl.create 100 in
  let _liveness_fact =
    {
      Flow.init_info = NameSet.empty;
      add_info = NameSet.union;
      changed =
        begin fun ~before ~after -> NameSet.(cardinal after > cardinal before)
        end;
      get = IntHashtbl.find gen_kill;
      set = IntHashtbl.add gen_kill;
    }
  in
  failwith ""
