open Ast
module M = CCMap.Make (String)

let rec widen_integer_types ?(initialization = false) =
  let ( let* ) = Option.bind in
  function
  | TInteger64, (TInteger64 | TInteger32 | TInteger16)
  | (TInteger32 | TInteger16), TInteger64 ->
    Some TInteger64
  | TInteger32, TInteger16 | TInteger16, TInteger32 -> Some TInteger32
  | TInteger16, TInteger16 -> Some TInteger16
  | TArray (typ1, min_bound1, max_bound1), TArray (typ2, min_bound2, max_bound2)
    when initialization && min_bound1 = min_bound2 && max_bound1 = max_bound2 ->
    let* typ = widen_integer_types ~initialization (typ1, typ2) in
    Some (TArray (typ, min_bound1, max_bound1))
  | TRecord fields1, TRecord fields2
    when initialization && List.length fields1 = List.length fields2 ->
    let* fields =
      CCList.all_some
        (List.map
           (fun ((s1, ty1), (s2, ty2)) ->
             if s1 = s2 then
               let* ty = widen_integer_types ~initialization (ty1, ty2) in
               Some (s1, ty)
             else None)
           (List.combine fields1 fields2))
    in
    Some (TRecord fields)
  | _ -> None

let rec widen_float_types ?(initialization = false) =
  let ( let* ) = Option.bind in
  function
  | TDouble, TDouble | TDouble, TSingle | TSingle, TDouble -> Some TDouble
  | TSingle, TSingle -> Some TSingle
  | TArray (typ1, min_bound1, max_bound1), TArray (typ2, min_bound2, max_bound2)
    when initialization && min_bound1 = min_bound2 && max_bound1 = max_bound2 ->
    let* typ = widen_float_types ~initialization (typ1, typ2) in
    Some (TArray (typ, min_bound1, max_bound1))
  | TRecord fields1, TRecord fields2
    when initialization && List.length fields1 = List.length fields2 ->
    let* fields =
      CCList.all_some
        (List.map
           (fun ((s1, ty1), (s2, ty2)) ->
             if s1 = s2 then
               let* ty = widen_float_types ~initialization (ty1, ty2) in
               Some (s1, ty)
             else None)
           (List.combine fields1 fields2))
    in
    Some (TRecord fields)
  | _ -> None

let rec widen_expression widened_typ (exp : Typed.expr) =
  match (widened_typ, snd exp) with
  | _, Int _ | _, Double _ | _, Var _ -> (widened_typ, snd exp)
  | _, Bool _ | _, Char _ | _, String _ -> exp
  | TArray (typ, _, _), Array (init, size) ->
    (widened_typ, Array (widen_expression typ init, size))
  | _, Array _ ->
    failwith
    @@ Format.asprintf "Type %a doesn't match array %a" pp_typ widened_typ
         Typed.pp_expr exp
  | _, Uop (uop, e) -> (widened_typ, Uop (uop, widen_expression widened_typ e))
  | _, Bop (bop, e1, e2) ->
    ( widened_typ,
      Bop (bop, widen_expression widened_typ e1, widen_expression widened_typ e2)
    )
  | TPointer typ, Addrof e -> (widened_typ, Addrof (widen_expression typ e))
  | _, Addrof _ ->
    failwith
    @@ Format.asprintf "Type %a doesn't match address of %a" pp_typ widened_typ
         Typed.pp_expr exp
  | _, Deref e ->
    (widened_typ, Deref (widen_expression (TPointer widened_typ) e))
  | _, ArrayIndex (arr, idx) ->
    let array_typ =
      match fst arr with
      | TArray (_, min_bound, max_bound) ->
        TArray (widened_typ, min_bound, max_bound)
      | typ ->
        failwith
        @@ Format.asprintf "widen_expression: invalid array typ: %a" pp_typ typ
    in
    (widened_typ, ArrayIndex (widen_expression array_typ arr, idx))
  | _, RecordField (record, field) ->
    let record_typ =
      match fst record with
      | TRecord fields ->
        TRecord
          (List.map
             (fun (field', typ) ->
               (field', if field = field' then widened_typ else typ))
             fields)
      | typ ->
        failwith
        @@ Format.asprintf "widen_expression: invalid record typ: %a" pp_typ typ
    in
    (widened_typ, RecordField (widen_expression record_typ record, field))
  | _, Call (_, _) -> (widened_typ, snd exp)

let typ_of_integer i =
  if i <= 32767 && i >= -32768 then TInteger16
  else if i <= Int32.to_int Int32.max_int && i >= Int32.to_int Int32.min_int
  then TInteger32
  else TInteger64

let is_exact_c_float x =
  let f32_bits = Int32.bits_of_float x in
  let round_tripped = Int32.float_of_bits f32_bits in
  Float.equal x round_tripped || (Float.is_nan x && Float.is_nan round_tripped)

let typ_of_double d = if is_exact_c_float d then Ast.TSingle else TDouble

let args_equal xs1 xs2 =
  List.length xs1 = List.length xs2
  && List.for_all
       (fun (arg1, arg2) ->
         match
           (widen_integer_types (arg1, arg2), widen_float_types (arg1, arg2))
         with
         | None, None -> arg1 = arg2
         | _ -> true)
       (List.combine xs1 xs2)

let rec check_expr ?(inside_selector = false) venv fenv = function
  | Int i -> (typ_of_integer i, Typed.Int i)
  | Bool b -> (TBoolean, Bool b)
  | Double d -> (typ_of_double d, Double d)
  | Char c -> (TChar, Char c)
  | String s -> (TArray (TChar, 0, String.length s), String s)
  | Var v ->
    begin try (M.find v venv, Var v)
    with Not_found ->
      failwith @@ Format.asprintf "Couldn't find variable %s" v
    end
  | Array (init_expr, size) ->
    let init_expr = check_expr venv fenv init_expr in
    (TArray (fst init_expr, 0, size), Array (init_expr, size))
  | Uop (uop, e) ->
    let ((typ, _) as e) = check_expr venv fenv e in
    (typ, Uop (uop, e))
  | Bop (bop, l, r) ->
    let ((l_typ, _) as l_expr) = check_expr venv fenv l in
    let ((r_typ, _) as r_expr) = check_expr venv fenv r in
    begin match bop with
    | Add | Sub | Mul | Div ->
      begin match
        (widen_integer_types (l_typ, r_typ), widen_float_types (l_typ, r_typ))
      with
      | Some typ', _ | _, Some typ' ->
        widen_expression typ' (typ', Bop (bop, l_expr, r_expr))
      | None, None ->
        if
          l_typ <> TInteger64 && l_typ <> TInteger32 && l_typ <> TInteger16
          && l_typ <> TSingle && l_typ <> TDouble
        then
          failwith
            (Format.asprintf
               "Left expression is different, expected %a or %a got %a" pp_typ
               TInteger64 pp_typ TDouble pp_typ l_typ);
        if r_typ <> l_typ then
          failwith
            (Format.asprintf "Right expression is different, expected %a got %a"
               pp_typ l_typ pp_typ r_typ);
        (l_typ, Bop (bop, l_expr, r_expr))
      end
    | And | Or ->
      if l_typ <> TBoolean then
        failwith
          (Format.asprintf "Left expression is different, expected %a got %a"
             pp_typ TBoolean pp_typ l_typ);
      if r_typ <> TBoolean then
        failwith
          (Format.asprintf "Right expression is different, expected %a got %a"
             pp_typ TBoolean pp_typ r_typ);
      (TBoolean, Bop (bop, l_expr, r_expr))
    | Eq | Neq | Lt | Le | Gt | Ge ->
      if
        l_typ <> TInteger64 && l_typ <> TInteger32 && l_typ <> TInteger16
        && l_typ <> TSingle && l_typ <> TDouble && l_typ <> TChar
      then
        failwith
          (Format.asprintf
             "Left expression is different, expected %a or %a got %a" pp_typ
             TInteger64 pp_typ TDouble pp_typ l_typ);
      if
        Option.is_some (widen_integer_types (l_typ, r_typ))
        || Option.is_some (widen_float_types (l_typ, r_typ))
        || r_typ = l_typ
      then (TBoolean, Bop (bop, l_expr, r_expr))
      else
        failwith
          (Format.asprintf "Right expression is different, expected %a got %a"
             pp_typ l_typ pp_typ r_typ)
    end
  | Call (f, xs) ->
    let xs = List.map (check_expr venv fenv) xs in
    begin match M.find f fenv with
    | xs', Some ret when args_equal (List.map fst xs) xs' -> (ret, Call (f, xs))
    | _ -> failwith "Different args"
    | exception Not_found ->
      begin match M.find f venv with
      | TFunction (xs', Some ret) when args_equal (List.map fst xs) xs' ->
        (ret, Call (f, xs))
      | typ -> failwith @@ Format.asprintf "Different type %a" pp_typ typ
      | exception Not_found ->
        failwith @@ Format.asprintf "Couldn't find function %s" f
      end
    end
  | ArrayIndex (expr, index) ->
    let expr = check_expr ~inside_selector:true venv fenv expr in
    let index = check_expr venv fenv index in
    let result =
      if inside_selector then Typed.ArrayIndex (expr, (TInteger64, snd index))
      else Typed.Deref (fst expr, ArrayIndex (expr, (TInteger64, snd index)))
    in
    begin match (expr, index) with
    | ( (TArray (array_typ, min_bound, max_bound), _),
        ((TInteger64 | TInteger32 | TInteger16), Int i) ) ->
      if i >= min_bound && i < max_bound then (array_typ, result)
      else failwith (Format.sprintf "array index out of bounds: %d" i)
    | (TArray (array_typ, _, _), _), ((TInteger64 | TInteger32 | TInteger16), _)
      ->
      (array_typ, result)
    | _ ->
      failwith
        (Format.asprintf "invalid types for array index: %a and %a" pp_typ
           (fst expr) pp_typ (fst index))
    end
  | RecordField (expr, field) ->
    let expr = check_expr ~inside_selector:true venv fenv expr in
    let result =
      if inside_selector then Typed.RecordField (expr, field)
      else Typed.Deref (fst expr, RecordField (expr, field))
    in
    begin match expr with
    | TRecord fields, _ ->
      if List.mem_assoc field fields then (List.assoc field fields, result)
      else
        failwith
        @@ Format.asprintf "Field %s not in %a" field Ast.pp_typ (fst expr)
    | typ, _ ->
      failwith
      @@ Format.asprintf "Invalid record field %s on type %a" field Ast.pp_typ
           typ
    end
  | Deref expr ->
    begin match check_expr venv fenv expr with
    | (TPointer ty, _) as expr -> (ty, Deref expr)
    | _ -> failwith "Expected pointer type for deref"
    end
  | Addrof ((String _ | Array _) as expr) ->
    check_expr ~inside_selector venv fenv (Addrof (ArrayIndex (expr, Int 0)))
  | Addrof ((ArrayIndex _ | RecordField _) as expr) ->
    let typ, expr = check_expr ~inside_selector:true venv fenv expr in
    (TPointer typ, expr)
  | Addrof (Deref expr) -> check_expr ~inside_selector venv fenv expr
  | Addrof (Var _ as var) ->
    let var = check_expr venv fenv var in
    begin match fst var with
    | TArray (typ, _min_bound, _max_bound) ->
      (TPointer typ, ArrayIndex (var, (TInteger64, Typed.Int 0)))
    | TRecord _ as typ ->
      (TPointer typ, ArrayIndex (var, (TInteger64, Typed.Int 0)))
    | typ -> (TPointer typ, Addrof var)
    end
  | Addrof expr ->
    failwith
    @@ Format.asprintf "Cannot get address of expression %a" Ast.pp_expr expr

let assign_types ltyp rtyp k =
  match
    CCOption.or_
      (widen_integer_types ~initialization:true (ltyp, rtyp))
      ~else_:(widen_float_types ~initialization:true (ltyp, rtyp))
  with
  | Some typ' when ltyp <> typ' ->
    failwith
    @@ Format.asprintf "Error widening type %a to type %a" Ast.pp_typ rtyp
         Ast.pp_typ ltyp
  | Some _ -> k ()
  | None ->
    if ltyp <> rtyp then
      failwith
        (Format.asprintf "Right expression is different, expected %a got %a"
           pp_typ ltyp pp_typ rtyp);
    k ()

let rec check_stmt venv fenv = function
  | Declare (x, typ) -> (M.add x typ venv, Typed.Declare (x, typ))
  | Assign (Var x, e) ->
    let e = check_expr venv fenv e in
    begin match M.find_opt x venv with
    | Some x_typ ->
      assign_types x_typ (fst e) (fun () ->
          ( M.add x x_typ venv,
            Typed.Assign ((x_typ, Var x), widen_expression x_typ e) ))
    | None -> failwith @@ Format.asprintf "Undeclared variable %s" x
    end
  | Assign (x, e) ->
    let x = check_expr venv fenv x in
    let e = check_expr venv fenv e in
    assign_types (fst x) (fst e) (fun () ->
        (venv, Typed.Assign (x, widen_expression (fst x) e)))
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
      | TFunction (xs', (Some TVoid | None))
        when args_equal (List.map fst xs) xs' ->
        (venv, Call (f, xs))
      | typ -> failwith @@ Format.asprintf "Different type %a" pp_typ typ
      | exception Not_found ->
        failwith @@ Format.asprintf "Couldn't find function %s" f
      end
    end
  | Alloca (x, t, i) -> (M.add x (TPointer t) venv, Alloca (x, t, i))

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
        M.add f typ (add_args args venv),
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
  let venv =
    List.fold_left (fun m { id; typ; _ } -> M.add id typ m) M.empty p.globals
  in
  let fenv = List.fold_left insert_header M.empty p.decls in
  let decls = List.map (check_decl venv fenv) p.decls in
  let _, main = check_stmt venv fenv p.main in
  { globals = p.globals; decls; main }
