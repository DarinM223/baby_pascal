open Ast
module M = Map.Make (String)

let rec check_expr venv fenv = function
  | Int i -> (TInteger, Typed.Int i)
  | Bool b -> (TBoolean, Bool b)
  | Var v ->
    begin try (M.find v venv, Var v)
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
    let ((l_typ, _) as l_expr) = check_expr venv fenv l in
    let ((r_typ, _) as r_expr) = check_expr venv fenv r in
    if l_typ <> l_expected then
      failwith
        (Format.asprintf "Left expression is different, expected %a" pp_typ
           l_typ);
    if r_typ <> r_expected then
      failwith
        (Format.asprintf "Right expression is different, expected %a" pp_typ
           r_typ);
    (ret_expected, Bop (bop, l_expr, r_expr))
  | Call (f, xs) ->
    let xs = List.map (check_expr venv fenv) xs in
    begin match M.find f fenv with
    | xs', Some ret when List.map fst xs = xs' -> (ret, Call (f, xs))
    | _ -> failwith "Different args"
    | exception Not_found ->
      begin match M.find f venv with
      | TFunction (xs', Some ret) when List.map fst xs = xs' ->
        (ret, Call (f, xs))
      | typ -> failwith @@ Format.asprintf "Different type %a" pp_typ typ
      | exception Not_found ->
        failwith @@ Format.asprintf "Couldn't find function %s" f
      end
    end
  | Load expr ->
    begin match check_expr venv fenv expr with
    | (TPointer ty, _) as expr -> (ty, Load expr)
    | _ -> failwith "Expected pointer type for load"
    end

let rec check_stmt venv fenv = function
  | Assign (x, e) ->
    let e = check_expr venv fenv e in
    (M.add x (fst e) venv, Typed.Assign (x, e))
  | Group stmts ->
    let venv, stmts =
      List.fold_left_map (fun venv stmt -> check_stmt venv fenv stmt) venv stmts
    in
    (venv, Group stmts)
  | If (test, thn, els) ->
    let test = check_expr venv fenv test in
    if fst test <> TBoolean then failwith "Expected test to be boolean type";
    let venv, thn = check_stmt venv fenv thn in
    let venv, els = check_stmt venv fenv els in
    (venv, If (test, thn, els))
  | While (test, body) ->
    let test = check_expr venv fenv test in
    if fst test <> TBoolean then failwith "Expected test to be boolean type";
    let venv, body = check_stmt venv fenv body in
    (venv, While (test, body))
  | Call (f, xs) ->
    let xs = List.map (check_expr venv fenv) xs in
    begin match M.find f fenv with
    | xs', None when List.map fst xs = xs' -> (venv, Call (f, xs))
    | _ -> failwith "Different args"
    | exception Not_found ->
      begin match M.find f venv with
      | TFunction (xs', (Some TVoid | None)) when List.map fst xs = xs' ->
        (venv, Call (f, xs))
      | typ -> failwith @@ Format.asprintf "Different type %a" pp_typ typ
      | exception Not_found ->
        failwith @@ Format.asprintf "Couldn't find function %s" f
      end
    end
  | Alloca (x, t, i) -> (M.add x (TPointer t) venv, Alloca (x, t, i))
  | Store (lhs, rhs) ->
    let lhs = check_expr venv fenv lhs in
    let rhs = check_expr venv fenv rhs in
    if fst lhs <> TPointer (fst rhs) then
      failwith
        (Format.asprintf "Right expression is different, expected %a" pp_typ
           (TPointer (fst rhs)));
    (venv, Store (lhs, rhs))

let insert_header fenv = function
  | Procedure (f, xs, _) -> M.add f (List.map snd xs, None) fenv
  | Function (f, xs, ret, _) -> M.add f (List.map snd xs, Some ret) fenv

let check_decl venv fenv decl =
  let add_args args venv =
    List.fold_left (fun venv (arg, typ) -> M.add arg typ venv) venv args
  in
  let f, venv, typ, body, update =
    match decl with
    | Procedure (f, args, body) ->
      (f, add_args args venv, None, body, fun body -> Procedure (f, args, body))
    | Function (f, args, typ, body) ->
      ( f,
        add_args args venv,
        Some typ,
        body,
        fun body -> Function (f, args, typ, body) )
  in
  let venv, body = check_stmt venv fenv body in
  if M.find_opt f venv <> typ then
    failwith
    @@ Format.asprintf "Function return types do not match, expected %a got %a"
         (Format.pp_print_option pp_typ)
         typ
         (Format.pp_print_option pp_typ)
         (M.find_opt f venv);
  update body

let check_program p =
  let venv = List.fold_left (fun m (k, v) -> M.add k v m) M.empty p.globals in
  let fenv = List.fold_left insert_header M.empty p.decls in
  let decls = List.map (check_decl venv fenv) p.decls in
  let _, main = check_stmt venv fenv p.main in
  { globals = p.globals; decls; main }
