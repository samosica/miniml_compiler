open Syntax

type error =
  TypeError of { expected_ty : ty
               ; actual_ty : ty
               }
| TypeErrorVar of { expected_ty : ty
                  ; actual_ty : ty
                  }
| UndefinedVariable of id
| NotFunction of { expected_ty : ty }
| NonFunctionApplied of { actual_ty : ty }
| NonTupleApplied of { actual_ty : ty }
| IndexOutOfBound
               
exception Error of Location.t * error
exception Unify

let err loc err = raise (Error (loc, err))

let print_error ~is_interactive lexbuf = function
  | Error (loc, err) ->
     if not is_interactive then
       (let pos = lexbuf.Lexing.lex_curr_p in
        let file_name = pos.Lexing.pos_fname in
        let line_num = loc.Location.loc_start.Lexing.pos_lnum in
        let col_start = loc.Location.loc_start.Lexing.pos_cnum - loc.Location.loc_start.Lexing.pos_bol in
        let col_end = loc.Location.loc_end.Lexing.pos_cnum - loc.Location.loc_start.Lexing.pos_bol in
        Printf.printf "File \"%s\", line %d, characters %d-%d:" file_name line_num col_start col_end;
        print_newline()
       );
     if is_interactive then Location.highlight lexbuf [loc];
     print_string "\027[91mError\027[0m: ";
     (match err with
       TypeError d -> print_string "This expression has type ";
                      pp_ty d.actual_ty;
                      print_string " but an expression was expected of type ";
                      pp_ty d.expected_ty;
                      print_newline()
     | TypeErrorVar d -> print_string "This variable has type ";
                         pp_ty d.actual_ty;
                         print_string " but an variable was expected of type ";
                         pp_ty d.expected_ty;
                         print_newline()
     | UndefinedVariable id -> Printf.printf "Variable not bound: %s" id;
                               print_newline()
     | NotFunction { expected_ty = expected_ty } ->
        print_string "This expression should not be a function, the expected type is ";
        pp_ty expected_ty;
        print_newline()
     | NonFunctionApplied { actual_ty = actual_ty } ->
        print_string "This expression has type ";
        pp_ty actual_ty;
        print_newline();
        print_endline "This is not a function; it cannot be applied."
     | NonTupleApplied { actual_ty = actual_ty } ->
        print_string "This expression has type ";
        pp_ty actual_ty;
        print_newline();
        print_endline "This is not a tuple; it cannot be applied."
     | IndexOutOfBound ->
        print_endline "Index out of bound")
  | _ -> ()
type tyenv = tysc Environment.t
           
let rec freevar_tyenv tyenv =
  let f tysc s = MySet.union (freevar_tysc tysc) s in
  Environment.fold_right f tyenv MySet.empty

type subst = (tyvar * ty) list
  
let rec subst_type (s : subst) ty =
  let rec subst_type' ty (var, t) =
    match ty, var with
    TyInt, _ -> TyInt
  | TyBool, _ -> TyBool
  | TyFun (ty1, ty2), _ -> TyFun (subst_type' ty1 (var, t),
                                  subst_type' ty2 (var, t))
  | TyTuple (ty1, ty2), _ -> TyTuple (subst_type' ty1 (var, t),
                                      subst_type' ty2 (var, t))                         
  | TyVar alpha, beta when alpha = beta -> t
  | _, _ -> ty
  in List.fold_left subst_type' ty s
   
let closure ty tyenv subst =
  let fv_tyenv' = freevar_tyenv tyenv in
  let fv_tyenv =
    MySet.bigunion
      (MySet.map
         (fun id -> freevar_ty (subst_type subst (TyVar id)))
         fv_tyenv') in
  let ids = MySet.diff (freevar_ty ty) fv_tyenv in
  TyScheme (MySet.to_list ids, ty)
   
let subst_eqs s eqs = List.map (fun (ty, ty') -> (subst_type s ty, subst_type s ty')) eqs
   
let rec unify = function
    [] -> []
  | ((ty1, ty2) as p) :: rest ->
     let rest = List.filter ((<>) p) rest in
     match ty1, ty2 with
       _, _ when ty1 = ty2 -> unify rest
     | TyFun (ty11, ty12), TyFun (ty21, ty22) ->
        unify ((ty11, ty21) :: (ty12, ty22) :: rest)
     | TyTuple (ty11, ty12), TyTuple (ty21, ty22) ->
        unify ((ty11, ty21) :: (ty12, ty22) :: rest)
     | TyVar alpha, _ ->
        if MySet.member alpha (freevar_ty ty2)
        then raise Unify
        else let q = (alpha, ty2) in
             let rest = subst_eqs [q] rest
             in q :: unify rest
     | _, TyVar alpha ->
        if MySet.member alpha (freevar_ty ty1)
        then raise Unify
        else let q = (alpha, ty1) in
             let rest = subst_eqs [q] rest
             in q :: unify rest
     | _, _ -> raise Unify

let incremental_unify s eqs =
  let eqs = subst_eqs s eqs in
  s @ unify eqs

let ty_prim op =
  match op with
    Plus -> (TyInt, TyInt, TyInt)
  | Mult -> (TyInt, TyInt, TyInt)
  | Lt -> (TyInt, TyInt, TyBool)
     
let rec ty_exp ?expected_ty ?expected_ty_in_recur tyenv subst exp =
  let expected_ty = match expected_ty with
      Some ty -> subst_type !subst ty
    | None -> TyVar (fresh_tyvar ()) in
  match exp.exp_desc with
    Var x ->
     let TyScheme (vars, ty) = try Environment.lookup x tyenv
                               with
                                 Environment.Not_bound -> err exp.exp_loc (UndefinedVariable x) in
     let s = List.map (fun id -> (id, TyVar (fresh_tyvar ()))) vars in
     let ty = ty |> subst_type s |> subst_type !subst in
     (try subst := incremental_unify !subst [(ty, expected_ty)]
      with
        Unify -> err exp.exp_loc (TypeError { expected_ty = expected_ty
                                            ; actual_ty   = ty }));
     subst_type !subst ty
  | ILit _ ->
     (try subst := incremental_unify !subst [(TyInt, expected_ty)]
      with
        Unify -> err exp.exp_loc (TypeError { expected_ty = expected_ty
                                            ; actual_ty   = TyInt }));
     TyInt
  | BLit _ ->
     (try subst := incremental_unify !subst [(TyBool, expected_ty)]
      with
        Unify -> err exp.exp_loc (TypeError { expected_ty = expected_ty
                                            ; actual_ty   = TyBool }));
     TyBool
  | BinOp (op, exp1, exp2) ->
     let (argty1, argty2, resty) = ty_prim op in
     let _ = ty_exp ~expected_ty:argty1 tyenv subst exp1 in
     let _ = ty_exp ~expected_ty:argty2 tyenv subst exp2 in
     let expected_ty = subst_type !subst expected_ty in
     (try subst := incremental_unify !subst [(resty, expected_ty)]
      with
        Unify -> err exp.exp_loc (TypeError { expected_ty = expected_ty
                                            ; actual_ty   = resty }));
     subst_type !subst resty
  | IfExp (exp1, exp2, exp3) ->
     let _ = ty_exp ~expected_ty:TyBool tyenv subst exp1 in
     let _ = ty_exp ~expected_ty ?expected_ty_in_recur tyenv subst exp2 in
     ty_exp ~expected_ty ?expected_ty_in_recur tyenv subst exp3
  | LetExp (id, _, e1, e2) ->
     let ty = ty_exp tyenv subst e1 in
     let tysc = closure ty tyenv !subst in
     let tyenv = Environment.extend id tysc tyenv in
     ty_exp ~expected_ty ?expected_ty_in_recur tyenv subst e2
  | LetRecExp (id, _, x, e1, e2) ->
     let argty = TyVar (fresh_tyvar ()) in
     let resty = TyVar (fresh_tyvar ()) in
     let tyenv' = Environment.extend id (tysc_of_ty (TyFun (argty, resty))) tyenv in
     let tyenv'' = Environment.extend x (tysc_of_ty argty) tyenv' in
     let _ = ty_exp ~expected_ty:resty tyenv'' subst e1 in
     let tysc = closure (subst_type !subst (TyFun (argty, resty))) tyenv !subst in
     let tyenv = Environment.extend id tysc tyenv in
     ty_exp ~expected_ty ?expected_ty_in_recur tyenv subst e2
  | FunExp (id, body) ->
     let domty = TyVar (fresh_tyvar ()) in
     let ranty = TyVar (fresh_tyvar ()) in
     let funty = TyFun (domty, ranty) in
     let () = try subst := incremental_unify !subst [(funty, expected_ty)]
              with
                Unify -> err exp.exp_loc (NotFunction { expected_ty = expected_ty }) in
     let domty = subst_type !subst domty in
     let tyenv' = Environment.extend id (tysc_of_ty domty) tyenv in
     let _ = ty_exp ~expected_ty:ranty tyenv' subst body in
     subst_type !subst funty
  | AppExp (exp1, exp2) ->
     let alpha = TyVar (fresh_tyvar ()) in
     let beta  = TyVar (fresh_tyvar ()) in
     let funty = TyFun (alpha, beta) in     
     let funty' = ty_exp tyenv subst exp1 in
     let () = try subst := incremental_unify !subst [(funty, funty')]
              with
                Unify -> err exp1.exp_loc (NonFunctionApplied { actual_ty = funty' }) in
     let _ = ty_exp ~expected_ty:alpha tyenv subst exp2 in
     (* これがないと，例えば，fun x -> if true then x else (fun y -> if x < 0 then true else false) 4 で適切なエラーが表示されない *)
     let expected_ty = subst_type !subst expected_ty in
     let beta = subst_type !subst beta in
     (try subst := incremental_unify !subst [(expected_ty, beta)]
      with
        Unify -> err exp.exp_loc (TypeError { expected_ty = expected_ty
                                            ; actual_ty   = beta }));
     subst_type !subst beta
  | TupleExp (e1, e2) ->
     let alpha = TyVar (fresh_tyvar ()) in
     let beta = TyVar (fresh_tyvar ()) in
     let tplty = TyTuple (alpha, beta) in
     let () = try subst := incremental_unify !subst [(expected_ty, tplty)]
              with
                Unify -> err exp.exp_loc (TypeError { expected_ty = expected_ty
                                                    ; actual_ty   = tplty }) in
     let _ = ty_exp ~expected_ty:alpha tyenv subst e1 in
     let _ = ty_exp ~expected_ty:beta tyenv subst e2 in
     subst_type !subst tplty
  | ProjExp (e, i, loc) ->
     let alpha = TyVar (fresh_tyvar ()) in
     let beta = TyVar (fresh_tyvar ()) in
     let tplty = TyTuple (alpha, beta) in
     let tplty' = ty_exp tyenv subst e in
     let _ = try subst := incremental_unify !subst [(tplty, tplty')]
             with
               Unify -> err e.exp_loc (NonTupleApplied { actual_ty = tplty' }) in
     let resty = match i with
         1 -> subst_type !subst alpha
       | 2 -> subst_type !subst beta
       | _ -> err loc IndexOutOfBound in
     let () = try subst := incremental_unify !subst [(resty, expected_ty)]
              with
                Unify -> err exp.exp_loc (TypeError { expected_ty = expected_ty
                                                    ; actual_ty = resty }) in
     resty
  | LoopExp (id, _, e1, e2) ->
     let ty = ty_exp tyenv subst e1 in
     let tysc = tysc_of_ty ty in
     let tyenv = Environment.extend id tysc tyenv in
     ty_exp ~expected_ty ~expected_ty_in_recur:ty tyenv subst e2     
  | RecurExp e ->
     let expected_ty_in_recur =
       match expected_ty_in_recur with
         None -> TyVar (fresh_tyvar ())
       | Some ty -> ty in
     let _ = ty_exp ~expected_ty:expected_ty_in_recur tyenv subst e in
     subst_type !subst expected_ty
     
let ty_exp tyenv exp = ty_exp tyenv (ref []) exp
