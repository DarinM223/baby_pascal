open Ast
module M = Map.Make (String)

let rec check_expr venv fenv = function
  | Int _ -> TInteger
  | Bool _ -> TBoolean
  | Var v ->
    begin try M.find v venv
    with Not_found ->
      failwith @@ Format.asprintf "Couldn't find variable %s" v
    end
  | Uop (_, e) -> check_expr venv fenv e
  | Bop (bop, l, r) ->
    let l_expected, r_expected, ret_expected =
      match bop with
      | Add | Sub | Mul | Div -> (TInteger, TInteger, TInteger)
      | And | Or -> (TBoolean, TBoolean, TBoolean)
      | Eq | Neq | Lt | Le | Gt | Ge -> (TInteger, TInteger, TBoolean)
    in
    let l_typ = check_expr venv fenv l in
    let r_typ = check_expr venv fenv r in
    if l_typ <> l_expected then
      failwith
        (Format.asprintf "Left expression is different, expected %a" pp_typ
           l_typ);
    if r_typ <> r_expected then
      failwith
        (Format.asprintf "Right expression is different, expected %a" pp_typ
           r_typ);
    ret_expected
  | Call (f, xs) ->
    let xs = List.map (check_expr venv fenv) xs in
    begin match M.find f fenv with
    | xs', Some ret when xs = xs' -> ret
    | _ -> failwith "Different args"
    | exception Not_found ->
      begin match M.find f venv with
      | TFunction (xs', Some ret) when xs = xs' -> ret
      | typ -> failwith @@ Format.asprintf "Different type %a" pp_typ typ
      | exception Not_found ->
        failwith @@ Format.asprintf "Couldn't find function %s" f
      end
    end

let rec check_stmt venv fenv = function
  | Assign (x, e) -> M.add x (check_expr venv fenv e) venv
  | Group stmts ->
    let venv = List.fold_left (fun venv -> check_stmt venv fenv) venv stmts in
    venv
  | If (test, thn, els) ->
    if check_expr venv fenv test <> TBoolean then
      failwith "Expected test to be boolean type";
    let venv = check_stmt venv fenv thn in
    let venv = check_stmt venv fenv els in
    venv
  | While (test, body) ->
    if check_expr venv fenv test <> TBoolean then
      failwith "Expected test to be boolean type";
    let venv = check_stmt venv fenv body in
    venv
  | Call (f, xs) ->
    let xs = List.map (check_expr venv fenv) xs in
    begin match M.find f fenv with
    | xs', None when xs = xs' -> venv
    | _ -> failwith "Different args"
    | exception Not_found ->
      begin match M.find f venv with
      | TFunction (xs', (Some TVoid | None)) when xs = xs' -> venv
      | typ -> failwith @@ Format.asprintf "Different type %a" pp_typ typ
      | exception Not_found ->
        failwith @@ Format.asprintf "Couldn't find function %s" f
      end
    end

let insert_header fenv = function
  | Procedure (f, xs, _) -> M.add f (List.map snd xs, None) fenv
  | Function (f, xs, ret, _) -> M.add f (List.map snd xs, Some ret) fenv

let check_decl venv fenv decl =
  let add_args args venv =
    List.fold_left (fun venv (arg, typ) -> M.add arg typ venv) venv args
  in
  let f, venv, typ, body =
    match decl with
    | Procedure (f, args, body) -> (f, add_args args venv, None, body)
    | Function (f, args, typ, body) -> (f, add_args args venv, Some typ, body)
  in
  let venv = check_stmt venv fenv body in
  if M.find_opt f venv <> typ then
    failwith
    @@ Format.asprintf "Function return types do not match, expected %a got %a"
         (Format.pp_print_option pp_typ)
         typ
         (Format.pp_print_option pp_typ)
         (M.find_opt f venv)

let check_program p =
  let venv = List.fold_left (fun m (k, v) -> M.add k v m) M.empty p.globals in
  let fenv = List.fold_left insert_header M.empty p.decls in
  List.iter (check_decl venv fenv) p.decls;
  ignore @@ check_stmt venv fenv p.main
