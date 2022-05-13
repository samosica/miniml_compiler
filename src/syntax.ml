exception Error of string
let err s = raise (Error s)

type id = string

type binOp = Plus | Mult | Lt

type exp = { exp_desc : exp_desc
           ; exp_loc  : Location.t
           }
and exp_desc =
  Var       of id
| ILit      of int
| BLit      of bool
| BinOp     of binOp * exp * exp
| IfExp     of exp * exp * exp
| LetExp    of id * Location.t * exp * exp
| FunExp    of id * exp
| AppExp    of exp * exp
| LetRecExp of id * Location.t * id * exp * exp
| LoopExp   of id * Location.t * exp * exp (* loop <id> = <exp> in <exp> *)
| RecurExp  of exp            (* recur <exp> *)
| TupleExp  of exp * exp      (* (<exp>, <exp>) *)
| ProjExp   of exp * int * Location.t      (* <exp> . <int> *)

let mkexp desc = { exp_desc = desc
                 ; exp_loc = Location.dummy_loc
                 }
             
(* ==== recur式が末尾位置にのみ書かれていることを検査 ==== *)

let recur_check e =
  let rec _recur_check e f = (* f: e が末尾位置にあるか *)
    match e.exp_desc with
      BinOp (_, e1, e2) -> _recur_check e1 false;
                           _recur_check e2 false
    | IfExp (e1, e2, e3) -> _recur_check e1 false;
                            _recur_check e2 f;
                            _recur_check e3 f
    | LetExp (_, _, e1, e2) -> _recur_check e1 false;
                               _recur_check e2 f
    | FunExp (_, e) -> _recur_check e false
    | AppExp (e1, e2) -> _recur_check e1 false;
                         _recur_check e2 false
    | LetRecExp (_, _, _, e1, e2) -> _recur_check e1 false;
                                     _recur_check e2 f
    | LoopExp (_, _, e1, e2) -> _recur_check e1 false;
                                _recur_check e2 true
    | RecurExp e ->
       if f then
         _recur_check e false
       else
         err "Error: recur"
    | TupleExp (e1, e2) -> _recur_check e1 false;
                           _recur_check e2 false
    | ProjExp (e, _, _) -> _recur_check e false
    | _ -> ()
  in _recur_check e false ;;

type tyvar = int

type ty =
  TyInt
| TyBool
| TyVar of tyvar
| TyFun of ty * ty
| TyTuple of ty * ty

type tysc = TyScheme of tyvar list * ty

let tysc_of_ty ty = TyScheme ([], ty)
                  
let rec pp_ty = function
    TyInt -> print_string "int"
  | TyBool -> print_string "bool"
  | TyVar n ->
     let c = Char.chr (n mod 26 + Char.code 'a') in
     let m = n / 26 in
     if m = 0
     then begin
         print_char '\'';
         print_char c
       end
     else begin
         print_char '\'';
         print_char c;
         print_int m
       end
  | TyFun (t1, t2) ->
     (match t1 with
        TyFun _ -> print_char '('; pp_ty t1; print_char ')'
      | _ -> pp_ty t1);
     print_string " -> ";
     pp_ty t2
  | TyTuple (t1, t2) ->
     (match t1 with
        TyFun _ -> print_char '('; pp_ty t1; print_char ')'
      | _ -> pp_ty t1);
     print_string " * ";
     (match t2 with
        TyFun _ -> print_char '('; pp_ty t2; print_char ')'
      | _ -> pp_ty t2)

let fresh_tyvar =
  let counter = ref 0 in
  let body () =
    let v = !counter in
    counter := v + 1; v
  in body
   
let rec freevar_ty ty =
  match ty with
    TyInt -> MySet.empty
  | TyBool -> MySet.empty
  | TyVar alpha -> MySet.singleton alpha
  | TyFun (ty1, ty2) ->
     MySet.union (freevar_ty ty1) (freevar_ty ty2)
  | TyTuple (ty1, ty2) ->
     MySet.union (freevar_ty ty1) (freevar_ty ty2)

let freevar_tysc = function
    TyScheme (tys, ty) -> MySet.diff (freevar_ty ty) (MySet.from_list tys)
