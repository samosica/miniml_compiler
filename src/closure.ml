open Pretty
module S = Syntax
module N = Normal
module Set = MySet

exception Error of string
let err s = raise (Error s)

type id = S.id
type binOp = S.binOp

let fresh_id = N.fresh_id

(* ==== 値 ==== *)
type value =
    Var  of id
  | IntV of int

(* ==== 式 ==== *)
type cexp =
    ValExp    of value
  | BinOp     of binOp * value * value
  | AppExp    of value * value list     (* NEW *)
  | IfExp     of value * exp * exp
  | TupleExp  of value list             (* NEW *)
  | ProjExp   of value * int

and exp =
    CompExp   of cexp
  | LetExp    of id * cexp * exp
  | LetRecExp of id * id list * exp * exp  (* NEW *)
  | LoopExp   of id * cexp * exp
  | RecurExp  of value

(* ==== Formatter ==== *)

let string_of_closure e =
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
  let pr_of_values = function
      [] -> text "()"
    | v :: vs' ->
        (text "(" <*>
         (List.fold_left
            (fun d v -> d <*> text "," <+> pr_of_value v)
            (pr_of_value v) vs')
         <*> (text ")"))
  in
  let pr_of_ids = function
      [] -> text "()"
    | id :: ids' ->
        (text "(" <*>
         (List.fold_left
            (fun d i -> d <*> text "," <+> text i)
            (text id) ids')
         <*> (text ")"))
  in
  let rec pr_of_cexp p e =
    let enclose p' e = if p' < p then text "(" <*> e <*> text ")" else e in
    match e with
      ValExp v -> pr_of_value v
    | BinOp (op, v1, v2) ->
        enclose 2 (pr_of_value v1 <+> pr_of_op op <+> pr_of_value v2)
    | AppExp (f, vs) ->
        enclose 3 (pr_of_value f <+> pr_of_values vs)
    | IfExp (v, e1, e2) ->
        enclose 1
          ((nest 2
              ((* group *) ((text "if 0 <")
                      <+> pr_of_value v
                      <+> text "then"
                      <|> pr_of_exp 1 e1))) <|>
           (nest 2
              ((* group *) (text "else" <|> pr_of_exp 1 e2))))
    | TupleExp vs -> pr_of_values vs
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
    | LetRecExp (id, parms, body, e) ->
        enclose 1
          ((nest 2 ((* group *) (text "let" <+> text "rec" <+> text id <+>
                           pr_of_ids parms <+>
                           text "=" <|> pr_of_exp 1 body)))
           <+> text "in" <|> pr_of_exp 1 e)
    | LoopExp (id, ce, e) ->
        enclose 1
          ((nest 2 ((* group *) (text "loop" <+> text id <+>
                           text "=" <|> pr_of_cexp 1 ce)))
           <+> text "in" <|> pr_of_exp 1 e)
    | RecurExp v ->
        enclose 3 (text "recur" <+> pr_of_value v)
  in layout (pretty 40 (pr_of_exp 0 e))

let tagged_id tag id = tag ^ id

let rec conv_val v bound_ids =
  match v with
  | N.Var i when List.mem i bound_ids -> Var i, Set.empty
  | N.Var i -> Var i, Set.singleton i
  | N.IntV i -> IntV i, Set.empty
and conv_cexp (c : N.cexp) bound_ids (k : cexp * id Set.t -> exp * id Set.t) =
  match c with
  | N.ValExp v ->
     let v, free_ids = conv_val v bound_ids in
     k (ValExp v, free_ids)
  | N.BinOp (op, v1, v2) ->
     let v1, free_ids  = conv_val v1 bound_ids in
     let v2, free_ids' = conv_val v2 bound_ids in
     k (BinOp (op, v1, v2), Set.union free_ids' free_ids)     
  | N.AppExp (v1, v2) ->
     let v1, free_ids  = conv_val v1 bound_ids in
     let v2, free_ids' = conv_val v2 bound_ids in
     (match v1 with
        Var id -> let tid = tagged_id "_r_" id in
                  let e, free_ids = k (AppExp (Var tid, [v1; v2]), Set.union free_ids' free_ids) in
                  LetExp (tid, ProjExp (Var id, 0), e), free_ids
      | _ -> raise (Failure "v1 must be a function"))
  | N.IfExp (v, e1, e2) ->
     let v, free_ids    = conv_val v  bound_ids in
     let e1, free_ids'  = conv_exp e1 bound_ids in
     let e2, free_ids'' = conv_exp e2 bound_ids in
     k (IfExp (v, e1, e2), Set.bigunion (Set.from_list [free_ids''; free_ids'; free_ids]))
  | N.TupleExp (v1, v2) ->
     let v1, free_ids  = conv_val v1 bound_ids in
     let v2, free_ids' = conv_val v2 bound_ids in
     k (TupleExp [v1; v2], Set.union free_ids' free_ids)     
  | N.ProjExp (v, i) ->
     let v, free_ids = conv_val v bound_ids in
     k (ProjExp (v, i - 1), free_ids)
and conv_exp (exp : N.exp) bound_ids =
  match exp with
  | N.CompExp c ->
     conv_cexp c bound_ids (fun (c', free_ids) -> CompExp c', free_ids)
  | N.LetExp (id, e1, e2) ->
     conv_cexp e1 bound_ids (fun (e1', free_ids) ->
         let e2', free_ids' = conv_exp e2 (id :: bound_ids) in
         LetExp (id, e1', e2'), Set.union free_ids' free_ids)
  | N.LetRecExp (id, x, e1, e2) ->
     let e1', free_ids = conv_exp e1 [id; x] in
     let e1' = Set.to_list free_ids
               |> List.mapi (fun k i -> (k + 1, i))
               |> List.fold_left (fun e (k, i) -> LetExp (i, ProjExp (Var id, k), e)) e1' in
     let e2', free_ids' = conv_exp e2 (id :: bound_ids) in
     let tid = tagged_id "_b_" id in
     let e2' = LetExp (id, TupleExp (Var tid :: List.map (fun i -> Var i) (Set.to_list free_ids)), e2') in
     LetRecExp (tid, [id; x], e1', e2'), Set.diff (Set.union free_ids' free_ids) (Set.from_list bound_ids)
  | N.LoopExp (id, e1, e2) ->
     conv_cexp e1 bound_ids (fun (e1', free_ids) ->
         let e2', free_ids' = conv_exp e2 (id :: bound_ids) in
         LoopExp (id, e1', e2'), Set.union free_ids' free_ids)
  | N.RecurExp v ->
     let v, free_ids = conv_val v bound_ids in
     RecurExp v, free_ids

let convert exp = conv_exp exp [] |> fst
