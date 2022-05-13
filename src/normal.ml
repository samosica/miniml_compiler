open Pretty
module S = Syntax

exception Error of string
let err s = raise (Error s)

type id = S.id
type binOp = S.binOp

let fresh_id = Misc.fresh_id_maker "_"

(* ==== 値 ==== *)
type value =
    Var  of id
  | IntV of int

(* ==== 式 ==== *)
type cexp =
    ValExp    of value
  | BinOp     of binOp * value * value
  | AppExp    of value * value
  | IfExp     of value * exp * exp
  | TupleExp  of value * value
  | ProjExp   of value * int

and exp =
    CompExp   of cexp
  | LetExp    of id * cexp * exp
  | LetRecExp of id * id * exp * exp
  | LoopExp   of id * cexp * exp
  | RecurExp  of value

(* ==== Formatter ==== *)

let string_of_norm e =
  let pr_of_op = function
      S.Plus -> text "+"
    | S.Mult -> text "*"
    | S.Lt -> text "<" in
  let pr_of_value = function
      Var id -> text id
    | IntV i ->
        let s = text (string_of_int i) in
        if i < 0 then text "(" <*> s <*> text ")" else s
  in
  let rec pr_of_cexp p e =
    let enclose p' e = if p' < p then text "(" <*> e <*> text ")" else e in
    match e with
      ValExp v -> pr_of_value v
    | BinOp (op, v1, v2) ->
        enclose 2 (pr_of_value v1 <+> pr_of_op op <+> pr_of_value v2)
    | AppExp (f, v) ->
        enclose 3 (pr_of_value f <+> pr_of_value v)
    | IfExp (v, e1, e2) ->
        enclose 1
          ((nest 2
              ((* group *) ((text "if 0 <")
                      <+> pr_of_value v
                      <+> text "then"
                      <|> pr_of_exp 1 e1))) <|>
           (nest 2
              ((* group *) (text "else" <|> pr_of_exp 1 e2))))
    | TupleExp (v1, v2) ->
        text "(" <*> pr_of_value v1 <*> text ","
        <+> pr_of_value v2 <*> text ")"
    | ProjExp (v, i) ->
        enclose 2 (pr_of_value v <*> text "." <*> text (string_of_int i))
  and pr_of_exp p e =
    let enclose p' e = if p' < p then text "(" <*> e <*> text ")" else e in
    match e with
      CompExp ce -> pr_of_cexp p ce
    | LetExp (id, ce, e) ->
        enclose 1
          ((nest 2 ((* group *) (text "let" <+> text id <+>
                           text "=" <|> pr_of_cexp 1 ce)))
           <+> text "in" <|> pr_of_exp 1 e)
    | LetRecExp (id, v, body, e) ->
        enclose 1
          ((nest 2 ((* group *) (text "let" <+> text "rec" <+>
                           text id <+> text v <+>
                           text "=" <|> pr_of_exp 1 body)))
           <+> text "in" <|> pr_of_exp 1 e)
    | LoopExp (id, ce, e) ->
        enclose 1
          ((nest 2 ((* group *) (text "loop" <+> text id <+>
                           text "=" <|> pr_of_cexp 1 ce)))
           <+> text "in" <|> pr_of_exp 1 e)
    | RecurExp v ->
        enclose 3 (text "recur" <+> pr_of_value v)
  in layout (pretty 30 (pr_of_exp 0 e))


(* ==== 正規形への変換 ==== *)
  
let rec norm_exp (e: Syntax.exp) (f: cexp -> exp) = match e.S.exp_desc with
    S.Var i -> f (ValExp (Var i))
  | S.ILit i -> f (ValExp (IntV i))
  | S.BLit true -> f (ValExp (IntV 1))
  | S.BLit false -> f (ValExp (IntV 0))
  | S.BinOp (op, e1, e2) ->
     let t1 = fresh_id "t" in
     let t2 = fresh_id "t" in
     norm_exp e1 (fun c1 ->
       norm_exp e2 (fun c2 ->
         LetExp (t1, c1, LetExp (t2, c2, f (BinOp (op, Var t1, Var t2))))))
  | S.IfExp (e1, e2, e3) ->
     let t1 = fresh_id "t" in
     norm_exp e1 (fun c1 ->
       LetExp (t1, c1, CompExp (IfExp (Var t1, norm_exp e2 f, norm_exp e3 f))))
  | S.LetExp (id, _, e1, e2) ->
     norm_exp e1 (fun c1 -> LetExp (id, c1, norm_exp e2 f))
  | S.FunExp (id, e) ->
     let f0 = fresh_id "f" in
     norm_exp (S.mkexp (S.LetRecExp (f0, Location.dummy_loc, id, e, S.mkexp (S.Var f0)))) f
  | S.AppExp (e1, e2) ->
     let t1 = fresh_id "t" in
     let t2 = fresh_id "t" in
     norm_exp e1 (fun c1 ->
       norm_exp e2 (fun c2 ->
         LetExp (t1, c1, LetExp (t2, c2, f (AppExp (Var t1, Var t2))))))
  | S.LetRecExp (id, _, x, e1, e2) ->
     LetRecExp (id, x, norm_exp e1 (fun c -> CompExp c), norm_exp e2 f)
  | S.LoopExp (id, _, e1, e2) ->
     norm_exp e1 (fun c1 ->
       LoopExp (id, c1, norm_exp e2 f))
  | S.RecurExp e ->
     let t0 = fresh_id "t" in
     norm_exp e (fun c ->
       LetExp (t0, c, RecurExp (Var t0)))
  | S.TupleExp (e1, e2) ->
     let t1 = fresh_id "t" in
     let t2 = fresh_id "t" in
     norm_exp e1 (fun c1 ->
       norm_exp e2 (fun c2 ->
         LetExp (t1, c1, LetExp (t2, c2, f (TupleExp (Var t1, Var t2))))))
  | S.ProjExp (e, i, _) ->
     let t0 = fresh_id "t" in
     norm_exp e (fun c ->
       LetExp (t0, c, f (ProjExp (Var t0, i))))       
and norm_exp' (e: Syntax.exp) (f: cexp -> exp) =
  let v k e = match e with
    | ValExp v -> k v
    | _ -> let t0 = fresh_id "t" in
           LetExp (t0, e, k (Var t0)) in
  match e.S.exp_desc with
    S.Var i -> f (ValExp (Var i))
  | S.ILit i -> f (ValExp (IntV i))
  | S.BLit true -> f (ValExp (IntV 1))
  | S.BLit false -> f (ValExp (IntV 0))
  | S.BinOp (op, e1, e2) ->
     norm_exp' e1 (v (fun v1 ->
       norm_exp' e2 (v (fun v2 ->
         f (BinOp (op, v1, v2))))))
  | S.IfExp (e1, e2, e3) ->
     norm_exp' e1 (v (fun v1 -> CompExp (IfExp (v1, norm_exp' e2 f, norm_exp' e3 f))))
  | S.LetExp (id, _, e1, e2) ->
     norm_exp' e1 (fun c1 -> LetExp (id, c1, norm_exp' e2 f))
  | S.FunExp (id, e) ->
     let f0 = fresh_id "f" in
     norm_exp' (S.mkexp (S.LetRecExp (f0, Location.dummy_loc, id, e, S.mkexp(S.Var f0)))) f
  | S.AppExp (e1, e2) ->
     norm_exp' e1 (v (fun v1 ->
       norm_exp' e2 (v (fun v2 ->
         f (AppExp (v1, v2))))))
  | S.LetRecExp (id, _, x, e1, e2) ->
     LetRecExp (id, x, norm_exp' e1 (fun c -> CompExp c), norm_exp' e2 f)
  | S.LoopExp (id, _, e1, e2) ->
     norm_exp' e1 (fun c1 ->
       LoopExp (id, c1, norm_exp' e2 f))
  | S.RecurExp e ->
     norm_exp' e (v (fun v -> RecurExp v))
  | S.TupleExp (e1, e2) ->
     norm_exp' e1 (v (fun v1 ->
       norm_exp' e2 (v (fun v2 ->
         f (TupleExp (v1, v2))))))
  | S.ProjExp (e, i, _) ->
     norm_exp' e (v (fun v -> f (ProjExp (v, i))))
(* and normalize e = norm_exp e (fun ce -> CompExp ce) *)
and normalize e = norm_exp' e (fun ce -> CompExp ce)

(* ==== entry point ==== *)
let convert prog =
  normalize prog
