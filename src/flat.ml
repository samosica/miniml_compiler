open Pretty
module S = Syntax
module C = Closure

exception Error of string
let err s = raise (Error s)

type id = S.id
type binOp = S.binOp

(* ==== 値 ==== *)
type value =
    Var  of id
  | Fun  of id   (* NEW *)
  | IntV of int

(* ==== 式 ==== *)
type cexp =
    ValExp    of value
  | BinOp     of binOp * value * value
  | AppExp    of value * value list
  | IfExp     of value * exp * exp
  | TupleExp  of value list
  | ProjExp   of value * int

and exp =
    CompExp   of cexp
  | LetExp    of id * cexp * exp
  | LoopExp   of id * cexp * exp
  | RecurExp  of value

let fresh_id = Normal.fresh_id
               
(* ==== 関数宣言 ==== *)
type decl = RecDecl of id * id list * exp  (* NEW *)

(* ==== プログラム ==== *)
type prog = decl list  (* NEW *)

(* ==== Formatter ==== *)

let string_of_flat prog =
  let pr_of_op = function
      S.Plus -> text "+"
    | S.Mult -> text "*"
    | S.Lt -> text "<" in
  let pr_of_value = function
      Var id -> text id
    | Fun id -> text "#'" <*> text id
    | IntV i ->
        let s = text (string_of_int i) in
        if i < 0 then text "(" <*> s <*> text ")" else s
  in
  let pr_of_values = function
      [] -> text "()"
    | v :: vs' ->
        text "(" <*>
        (List.fold_left
           (fun d v -> d <*> text "," <+> pr_of_value v)
           (pr_of_value v) vs')
        <*> (text ")")
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
    | LoopExp (id, ce, e) ->
        enclose 1
          ((nest 2 ((* group *) (text "loop" <+> text id <+>
                           text "=" <|> pr_of_cexp 1 ce)))
           <+> text "in" <|> pr_of_exp 1 e)
    | RecurExp v ->
        enclose 3 (text "recur" <+> pr_of_value v)
  in
  let pr_of_decl = function
      RecDecl (id, params, body) ->
        let tparms = match params with
            [] -> text ""
          | param :: params' ->
              List.fold_left (fun t p -> t <*> text "," <+> text p)
                (text param) params'
        in
        ((* group *) (text "let" <+> text "rec" <+>
                ((* group *)
                   ((text id) <+> text "(" <*> tparms <*> text ")" <+>
                    nest 2 (text "=" <|> pr_of_exp 1 body)))))
  in
  layout
    (pretty 30 (List.fold_right (fun decl doc ->
         pr_of_decl decl <|> nil <|> doc) prog nil))

(* ==== フラット化：変数参照と関数参照の区別も同時に行う ==== *)

let rec flat_val env = function
  | C.Var i -> (try Environment.lookup i env
                with
                  Environment.Not_bound -> raise (Failure ("Variable not bound: " ^ i)))
  | C.IntV i -> IntV i
and flat_cexp env prog = function
    C.ValExp v -> ValExp (flat_val env v)
  | C.BinOp (op, v1, v2) -> BinOp (op, flat_val env v1, flat_val env v2)
  | C.AppExp (v, vs) -> AppExp (flat_val env v, List.map (flat_val env) vs)
  | C.IfExp (v, e1, e2) -> IfExp (flat_val env v, flat_exp env prog e1, flat_exp env prog e2)
  | C.TupleExp vs -> TupleExp (List.map (flat_val env) vs)
  | C.ProjExp (v, i) -> ProjExp (flat_val env v, i)
and flat_exp env prog = function
    C.CompExp c -> CompExp (flat_cexp env prog c)
  | C.LetExp (id, e1, e2) ->
     LetExp (id, flat_cexp env prog e1, flat_exp (Environment.extend id (Var id) env) prog e2)
  | C.LetRecExp (id, args, e1, e2) ->
     let id' = if List.exists (fun (RecDecl (id'', _, _)) -> id'' = id) !prog 
               then fresh_id ("f_" ^ id) (* 関数名の重複を取り除く *)
               else id in
     let env = Environment.extend id (Fun id') env in
     let env' = List.fold_left (fun env arg -> Environment.extend arg (Var arg) env) env args in
     let e1 = flat_exp env' prog e1 in
     prog := RecDecl (id', args, e1) :: !prog;
     flat_exp env prog e2
  | C.LoopExp (id, e1, e2) ->
     LoopExp (id, flat_cexp env prog e1, flat_exp (Environment.extend id (Var id) env) prog e2)
  | C.RecurExp v -> RecurExp (flat_val env v)
and flatten exp =
  let prog = ref [] in
  let exp = flat_exp Environment.empty prog exp in
  List.rev (RecDecl ("_toplevel", ["p0"; "p1"], exp) :: !prog)
