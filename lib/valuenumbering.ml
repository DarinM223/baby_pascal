module InstrHashtbl = Hashtbl.Make (struct
  type t = Normalize.Target.instr
  let equal = Normalize.Target.equal_instr
  let hash = Hashtbl.hash
end)

module Make (Dom : Dominator.S with type label = Normalize.Cfg.label) = struct
  type value_num = Normalize.Name.t
  module NameHashtbl = Hashtbl.Make (struct
    type t = value_num
    let equal = Normalize.Name.equal
    let hash = Hashtbl.hash
  end)
  type state = {
    instr_of_vn : Undag.Target.instr NameHashtbl.t;
        (** Used for instruction simplification *)
    vn : value_num NameHashtbl.t;  (** Value number of variable *)
    vn_of_expr : value_num InstrHashtbl.t;
        (** Hashtable for getting value number from hashed instruction *)
  }

  let init_state () =
    {
      instr_of_vn = NameHashtbl.create Utils.hashtbl_size;
      vn = NameHashtbl.create Utils.hashtbl_size;
      vn_of_expr = InstrHashtbl.create Utils.hashtbl_size;
    }

  open struct
    let iter_defs f i =
      ignore
      @@ Normalize.Target.map_defs
           (function
             | Reg r ->
               f r;
               Reg r
             | op -> op)
           i
  end

  let rec dvnt (state : state) (tree : Dom.tree) (graph : Normalize.Cfg.graph) :
      Normalize.Cfg.graph =
    let keys = CCVector.create () in
    let blank_out = Normalize.Target.(map_defs (Fun.const tombstone)) in
    let add_vn k v = NameHashtbl.replace state.vn k v in
    let add_expr expr v =
      let expr = blank_out expr in
      InstrHashtbl.add state.vn_of_expr expr v;
      CCVector.push keys expr
    in
    let lookup_expr expr =
      InstrHashtbl.find_opt state.vn_of_expr (blank_out expr)
    in
    let zgraph, graph =
      Normalize.Cfg.(focus (idd (Dom.tree_label tree)) graph)
    in
    let first, tail = Normalize.Cfg.goto_start zgraph in
    let go_first graph = function
      | Normalize.Cfg.Entry -> (Normalize.Cfg.Entry, graph)
      | Label (l, info) ->
        let pos = Dom.position_of_label (Some l) in
        let preds = Dom.predecessors pos in
        (* If backedge exists, don't bother rewriting phis *)
        if List.exists (Dom.dominates pos) preds then begin
          List.iter (fun n -> add_vn n n) info.args;
          (Label (l, info), graph)
        end
        else
          (* Remove meaningless or redundant phis by getting
             zippers into every predecessor of the block, modifying
             them in place, then inserting them back into the graph *)
          let zippers, graph =
            preds
            |> List.map (fun pos ->
                Normalize.Cfg.idd (Dom.label_of_position pos))
            |> List.fold_left
                 (fun (zippers, graph) pred ->
                   let zblock, graph = Normalize.Cfg.focus pred graph in
                   (Normalize.Cfg.goto_end zblock :: zippers, graph))
                 ([], graph)
          in
          let rewrite_arg (zippers, args) arg =
            (* todo: if all zipper's jump arg at that position is the same,
               remove them from all zippers, and set vn for arg to it *)
            add_vn arg arg;
            (zippers, arg :: args)
          in
          let zippers, args =
            List.fold_left rewrite_arg (zippers, []) info.args
          in
          let graph =
            List.fold_left
              (fun graph (head, last) ->
                Normalize.Cfg.unfocus ((head, Last last), graph))
              graph zippers
          in
          (Label (l, { info with args = List.rev args }), graph)
    in
    let go_instruction instr =
      let rec rewrite_with_value_number = function
        | Normalize.Target.Const i -> Normalize.Target.Const i
        | Reg r ->
          begin try Reg (NameHashtbl.find state.vn r) with Not_found -> Reg r
          end
        | Label (lab, args) ->
          Label (lab, List.map rewrite_with_value_number args)
      in
      let instr' =
        instr
        |> Normalize.Target.map_uses rewrite_with_value_number
        |> Undag.treeify_instruction (NameHashtbl.find_opt state.instr_of_vn)
        |> Simplify.simplify_instruction
      in
      iter_defs
        (fun def -> NameHashtbl.replace state.instr_of_vn def instr')
        instr;
      let instr' = Simplify.convert_instruction instr' in
      Logs.debug (fun m ->
          m "%a simplified into %a\n" Normalize.Target.pp_instr instr
            Normalize.Target.pp_instr instr');
      begin match lookup_expr instr' with
      | Some vn ->
        iter_defs
          (fun def ->
            Logs.debug (fun m ->
                m "Adding value number %a <- %a\n" Normalize.Target.pp_reg def
                  Normalize.Target.pp_reg vn);
            add_vn def vn)
          instr';
        if Normalize.Target.is_side_effectful instr' then Some instr' else None
      | None ->
        iter_defs
          (fun def ->
            Logs.debug (fun m ->
                m "Adding value number %a <- %a\n" Normalize.Target.pp_reg def
                  Normalize.Target.pp_reg def);
            add_vn def def;
            Logs.debug (fun m ->
                m "Adding expression %a <- %a\n" Normalize.Target.pp_instr
                  instr' Normalize.Target.pp_reg def);
            add_expr instr' def)
          instr';
        Some instr'
      end
    in
    let rec go_tail = function
      | Normalize.Cfg.Tail (Instruction instr, tail) ->
        begin match go_instruction instr with
        | Some instr -> Normalize.Cfg.Tail (Instruction instr, go_tail tail)
        | None -> go_tail tail
        end
      | Last l ->
        begin match l with
        | Exit -> Last Exit
        | Branch (instr, l) ->
          let instr = Option.value ~default:instr (go_instruction instr) in
          Last (Branch (instr, l))
        | CBranch (instr, l1, l2) ->
          let instr = Option.value ~default:instr (go_instruction instr) in
          Last (CBranch (instr, l1, l2))
        | Return instr ->
          let instr = Option.value ~default:instr (go_instruction instr) in
          Last (Return instr)
        end
    in
    let first, graph = go_first graph first in
    let tail = go_tail tail in
    let graph = Normalize.Cfg.unfocus ((First first, tail), graph) in
    let graph =
      List.fold_left (Fun.flip (dvnt state)) graph (Dom.tree_children tree)
    in
    (* Pop newly added expressions in scope *)
    CCVector.iter (InstrHashtbl.remove state.vn_of_expr) keys;
    graph
end
