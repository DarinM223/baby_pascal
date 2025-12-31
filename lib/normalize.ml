module StringSet = struct
  include Set.Make (String)

  let pp fmt s =
    Format.fprintf fmt "S.of_list %s" ([%show: string list] (elements s))
end

module Target = struct
  type label = int * string
  type reg = string [@@deriving show]
  type info = {
    uses : StringSet.t;
    defs : StringSet.t;
  }
  [@@deriving show]
  type instr = info * string [@@deriving show]

  type cond =
    | LT
    | LE
    | GT
    | GE
    | EQ
    | NE

  let init_info = { uses = StringSet.empty; defs = StringSet.empty }

  let goto (_, label) = (init_info, "j " ^ label)
  let cbranch ~uses (cond : cond) (_, l1) l2 =
    let instr =
      match cond with
      | LT -> "jl "
      | LE -> "jle "
      | GT -> "jg "
      | GE -> "jge "
      | EQ -> "jz "
      | NE -> "jnz "
    in
    ( { init_info with uses = StringSet.of_list uses },
      instr ^ l1 ^ "\n" ^ snd (goto l2) )
  let return ~uses:_ = (init_info, "ret")
end

module Cfg = Graph.Make (Target)

let normalize (stmts : Ast.stmt list) : Cfg.graph =
  let new_label : unit -> Cfg.label =
    let c = ref (-1) in
    fun () ->
      let i =
        incr c;
        !c
      in
      (i, "label" ^ string_of_int i)
  in
  let rec go_stmt (_next : Cfg.label) (_stmt : Ast.stmt) : Cfg.nodes =
    failwith ""
  in
  Cfg.unfocus
  @@ List.fold_right
       (fun stmt acc ->
         let next = new_label () in
         go_stmt next stmt @@ Cfg.label next @@ acc)
       stmts
       Cfg.(entry empty)
