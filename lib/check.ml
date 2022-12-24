open Ast
module M = Map.Make (String)

let rec check_expr venv fenv = function
  | Int _ -> TInteger
  | Bool _ -> TBoolean
  | Var v -> M.find v venv
  | Uop (_, e) -> check_expr venv fenv e
  | Bop (_, l, r) ->
      let typ = check_expr venv fenv l in
      if typ <> check_expr venv fenv r then
        failwith "Left and right expressions are different";
      typ
  | Call (f, xs) -> (
      let xs = List.map (check_expr venv fenv) xs in
      match M.find f fenv with
      | xs', Some ret when xs = xs' -> ret
      | _ -> failwith "Different args")

let rec check_stmt venv fenv f = function
  | Assign (x, e) -> M.add x (check_expr venv fenv e) venv
  | Return e -> (
      let ret_typ = Option.map (check_expr venv fenv) e in
      match M.find f fenv with
      | _, ret when ret = ret_typ -> venv
      | _ -> failwith "Different return type")
  | If (test, thn, els) ->
      if check_expr venv fenv test <> TBoolean then
        failwith "Expected test to be boolean type";
      let _ = List.fold_left (fun venv -> check_stmt venv fenv f) venv thn in
      let _ = List.fold_left (fun venv -> check_stmt venv fenv f) venv els in
      venv
  | While (test, body) ->
      if check_expr venv fenv test <> TBoolean then
        failwith "Expected test to be boolean type";
      let _ = List.fold_left (fun venv -> check_stmt venv fenv f) venv body in
      venv
  | Call (f, xs) -> (
      let xs = List.map (check_expr venv fenv) xs in
      match M.find f fenv with
      | xs', None when xs = xs' -> venv
      | _ -> failwith "Different args")

let insert_header fenv = function
  | Procedure (f, xs, _) -> M.add f (List.map snd xs, None) fenv
  | Function (f, xs, ret, _) -> M.add f (List.map snd xs, Some ret) fenv

let check_decl venv fenv = function
  | Procedure (f, _, body) ->
      ignore @@ List.fold_left (fun venv -> check_stmt venv fenv f) venv body
  | Function (f, _, _, body) ->
      let has_ret = ref false in
      let go_stmt venv e =
        (match e with Return _ -> has_ret := true | _ -> ());
        check_stmt venv fenv f e
      in
      let _ = List.fold_left go_stmt venv body in
      if not !has_ret then failwith "Function needs to have a return"

let check_program p =
  let venv = List.fold_left (fun m (k, v) -> M.add k v m) M.empty p.globals in
  let fenv = List.fold_left insert_header M.empty p.decls in
  List.iter (check_decl venv fenv) p.decls;
  let fenv = M.add "main" ([], None) fenv in
  ignore @@ List.fold_left (fun venv -> check_stmt venv fenv "main") venv p.main