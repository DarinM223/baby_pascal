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
  | Call (f, xs) ->
    let xs = List.map (check_expr venv fenv) xs in
    (match M.find f fenv with
    | xs', Some ret when xs = xs' -> ret
    | _ -> failwith "Different args")

let rec check_stmt venv fenv = function
  | Assign (x, e) -> M.add x (check_expr venv fenv e) venv
  | If (test, thn, els) ->
    if check_expr venv fenv test <> TBoolean then
      failwith "Expected test to be boolean type";
    let _ = List.fold_left (fun venv -> check_stmt venv fenv) venv thn in
    let _ = List.fold_left (fun venv -> check_stmt venv fenv) venv els in
    venv
  | While (test, body) ->
    if check_expr venv fenv test <> TBoolean then
      failwith "Expected test to be boolean type";
    let _ = List.fold_left (fun venv -> check_stmt venv fenv) venv body in
    venv
  | Call (f, xs) ->
    let xs = List.map (check_expr venv fenv) xs in
    (match M.find f fenv with
    | xs', None when xs = xs' -> venv
    | _ -> failwith "Different args")

let insert_header fenv = function
  | Procedure (f, xs, _) -> M.add f (List.map snd xs, None) fenv
  | Function (f, xs, ret, _) -> M.add f (List.map snd xs, Some ret) fenv

let check_decl venv fenv decl =
  let f, typ, body =
    match decl with
    | Procedure (f, _, body) -> (f, None, body)
    | Function (f, _, typ, body) -> (f, Some typ, body)
  in
  let venv = List.fold_left (fun venv -> check_stmt venv fenv) venv body in
  if M.find_opt f venv <> typ then failwith "Function return types do not match"

let check_program p =
  let venv = List.fold_left (fun m (k, v) -> M.add k v m) M.empty p.globals in
  let fenv = List.fold_left insert_header M.empty p.decls in
  List.iter (check_decl venv fenv) p.decls;
  ignore @@ List.fold_left (fun venv -> check_stmt venv fenv) venv p.main
