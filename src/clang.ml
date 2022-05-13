open Pretty
module S = Syntax

exception Error of string
let err s = raise (Error s)

type id = S.id
type binOp = S.binOp
type label = Vm.label

type ty = TyInt | TyPtr | TyFunPtr           

type value =
  Var of id
| Fun of id
| IntV of int
| ArraySubscript of value * int (* e.g. a[0] *)
| Accessor of value * ty (* e.g. x.i *)

type exp =
  ValExp of value
| BinOp of binOp * value * value
| FunCall of value * exp list
| Malloc of int (* e.g. (any* )malloc(sizeof(any) * 3) *)
| CastExp of exp * ty (* e.g. int_to_any(2 + x) *)

type stmt =
  Exp of exp
| Assign of value * exp       
| Label of label (* l: ; *)
| If of value * stmt
| Return of value
| Goto of label

(* 関数名, ローカル変数の個数, 本体 *)
type fn = Fn of id * int * stmt list

type prog = fn list

let local_access i = ArraySubscript (Var "local", i)

let string_of prog =
  let rec pr_of_val = function
      Var i -> text i
    | Fun i -> text i
    | IntV i -> text (string_of_int i)
    | ArraySubscript (v, i) -> 
       pr_of_val v <*> text "[" <*> text (string_of_int i) <*> text "]"
    | Accessor (v, ty) ->
       let mem = match ty with
           TyInt    -> "i"
         | TyPtr    -> "p"
         | TyFunPtr -> "f" in
       pr_of_val v <*> text "." <*> text mem in
  let pr_of_bop = function
      S.Plus -> text "+"
    | S.Mult -> text "*"
    | S.Lt   -> text "<" in
  let rec pr_of_exp = function
      ValExp v -> pr_of_val v
    | BinOp (bop, v1, v2) ->
       pr_of_val v1 <+> pr_of_bop bop <+> pr_of_val v2
    | FunCall (v, es) ->
       let d = match es with
           [] -> nil
         | e :: es' -> List.fold_left (fun d e -> d <*> text "," <+> pr_of_exp e) (pr_of_exp e) es' in
       pr_of_val v <*> text "(" <*> d <*> text ")"
    | Malloc n ->
       text "(any*)malloc(sizeof(any)" <+> text "*" <+> text (string_of_int n) <*> text ")"
    | CastExp (e, ty) ->
       let ty = match ty with
           TyInt -> "int"
         | TyPtr -> "ptr"
         | TyFunPtr -> "funptr" in
       text ty <*> text "_to_any(" <*> pr_of_exp e <*> text ")" in
  let rec pr_of_stmt = function
      Exp e -> pr_of_exp e <*> text ";"
    | Assign (v, e) ->
       pr_of_val v <+> text "=" <+> pr_of_exp e <*> text ";"
    | Label lbl -> nest 2 (text lbl <*> text ":" <+> text ";")
    | If (v, s) -> text "if(" <*> pr_of_val v <*> text ")" <*> nest 2 (text "{" <|> pr_of_stmt s) <|> text "}"
    | Return v -> text "return" <+> pr_of_val v <*> text ";"
    | Goto lbl -> text "goto" <+> text lbl <*> text ";" in
  let header =
    text "#include <stdlib.h>" <|>
    text "#include \"lib/any.h\"" in
  let pr_of_fun = function
      Fn (name, n, stmts) ->
      let args = if name = "_toplevel"
                 then "()"
                 else "(any p0, any p1)" in
      let stmts = match stmts with
          [] -> nil
        | s :: ss -> List.fold_left (fun d s -> d <|> pr_of_stmt s) (pr_of_stmt s) ss in
      let stmts =
        text "any" <+> text "local[" <*> text (string_of_int n) <*> text "];" <|> stmts in
      text "any" <+> text name <*> text args <*> nest 2 (text "{" <|> stmts) <|> text "}" in
  let pr_of_prog prog =
    let defs = match prog with
        [] -> nil
      | f :: fs ->
         List.fold_left (fun d f -> d <|> nil <|> pr_of_fun f) (pr_of_fun f) fs in
    header <|> nil <|> defs in
  layout 
    (pretty 30 (pr_of_prog prog))      

let gen_operand = function
    Vm.Param i -> Var ("p" ^ string_of_int i)
  | Vm.Local i -> local_access i
  | Vm.Proc l -> Fun l
  | Vm.IntV i -> IntV i

let operand_to_any op =
  let v = gen_operand op in
  match v with
    Fun _  -> CastExp (ValExp v, TyFunPtr)
  | IntV _ -> CastExp (ValExp v, TyInt)
  | _      -> ValExp v

let operand_to_ty op ty =
  let v = gen_operand op in
  match v, ty with
    Fun _ , TyFunPtr -> v
  | Fun _ , _        -> err "Type error"
  | IntV _, TyInt    -> v
  | IntV _, _        -> err "Type error"
  | _     , _        -> Accessor (v, ty)

let gen_instr = function
    Vm.Move (ofs, op) ->
     let e = operand_to_any op in
     [Assign (local_access ofs, e)]
  | Vm.BinOp (ofs, bop, op1, op2) ->
     let v1 = operand_to_ty op1 TyInt in
     let v2 = operand_to_ty op2 TyInt in
     let res = CastExp (BinOp (bop, v1, v2), TyInt) in
     [Assign (local_access ofs, res)]
  | Vm.Label lbl ->
     [Label lbl]
  | Vm.BranchIf (op, l) ->
     let v = operand_to_ty op TyInt in
     [If (v, Goto l)]
  | Vm.Goto lbl ->
     [Goto lbl]
  | Vm.Call (ofs, opf, ops) ->
     let f = operand_to_ty opf TyFunPtr in
     let args = List.map operand_to_any ops in
     [Assign (local_access ofs, FunCall (f, args))]
  | Vm.Return op ->
     [Return (gen_operand op)]
  | Vm.Malloc (ofs, ops) ->
     let v = Accessor (local_access ofs, TyPtr) in
     let instrs =
       List.mapi (fun i op -> Assign (ArraySubscript (v, i), operand_to_any op)) ops in
     Assign (local_access ofs, CastExp (Malloc (List.length ops), TyPtr)) :: instrs
  | Vm.Read (ofs, op, i) ->
     let v = operand_to_ty op TyPtr in
     [Assign (local_access ofs, ValExp (ArraySubscript (v, i)))]
  | _ -> err "Not implemented"

let gen_decl = function
    Vm.ProcDecl (name, n, instrs) ->
    Fn (name, n, List.concat (List.map gen_instr instrs))

let codegen vmprog =
  List.map gen_decl vmprog
