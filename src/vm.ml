module S = Syntax
module F = Flat

exception Error of string
let err s = raise (Error s)

type binOp = S.binOp

type id = int
type label = string

type operand =
    Param of int     (* param(n) *)
  | Local of id      (* local(ofs) *)
  | Proc  of label   (* labimm(l) *)
  | IntV  of int     (* imm(n) *)

type instr =
    Move of id * operand (* local(ofs) <- op *)
  | BinOp of id * S.binOp * operand * operand
    (* local(ofs) <- bop(op_1, op_2) *)
  | Label of label (* l: *)
  | BranchIf of operand * label (* if op then goto l *)
  | Goto of label (* goto l *)
  | Call of id * operand * operand list
    (* local(ofs) <- call op_f(op_1, ..., op_n) *)
  | Return of operand (* return(op) *)
  | Malloc of id * operand list (* new ofs [op_1, ..., op_n] *)
  | Read of id * operand * int (* read ofs #i(op) *)
  | BEGIN of label (* データフロー解析で内部的に使用 *)
  | END of label   (* データフロー解析で内部的に使用 *)

type decl =
    ProcDecl of label * int * instr list  (* int は局所変数の個数 *)

type prog = decl list

(* ==== Formatter ==== *)

let string_of_binop = function
    S.Plus -> "add"
  | S.Mult -> "mul"
  | S.Lt   -> "lt"

let string_of_operand = function
    Param i -> "p" ^ string_of_int i
  | Local o -> (* -1 は生存変数解析で使われる特殊な値 *)
      if o = -1 then "*" else "t" ^ string_of_int o
  | Proc  l -> l
  | IntV  i -> string_of_int i

let string_of_instr idt tab = function
    Move (t, v) ->
      idt ^ "move" ^ tab ^ "t" ^ string_of_int t ^ ", " ^
      string_of_operand v
  | BinOp (t, op, v1, v2) ->
      idt ^ string_of_binop op ^ tab ^ "t" ^ string_of_int t ^ ", " ^
      string_of_operand v1 ^ ", " ^ string_of_operand v2
  | Label lbl -> lbl ^ ":"
  | BranchIf (v, lbl) ->
      idt ^ "bif" ^ tab ^ string_of_operand v ^ ", " ^ lbl
  | Goto lbl ->
      idt ^ "goto" ^ tab ^ lbl
  | Call (dst, tgt, [a0; a1]) ->
      idt ^ "call" ^ tab ^ "t" ^ string_of_int dst ^ ", " ^
      string_of_operand tgt ^
      "(" ^ string_of_operand a0 ^ ", " ^ string_of_operand a1 ^ ")"
  | Call (_, _, args) -> err ("Illegal number of arguments: " ^
                              string_of_int (List.length args))
  | Return v ->
      idt ^ "ret" ^ tab ^ string_of_operand v
  | Malloc (t, vs) ->
      idt ^ "new" ^ tab ^ "t" ^ string_of_int t ^ " [" ^
      (String.concat ", " (List.map string_of_operand vs)) ^ "]"
  | Read (t, v, i) ->
      idt ^ "read" ^ tab ^ "t" ^ string_of_int t ^ " #" ^
      string_of_int i ^ "(" ^ string_of_operand v ^ ")"
  | BEGIN lbl ->
      idt ^ "<BEGIN: " ^ lbl ^ ">"
  | END lbl ->
      idt ^ "<END: " ^ lbl ^ ">"

let string_of_decl (ProcDecl (lbl, n, instrs)) =
  "proc " ^ lbl ^ "(" ^ string_of_int n ^ ") =\n" ^
  (String.concat "\n"
     (List.map (fun i -> string_of_instr "  " "\t" i) instrs)) ^ "\n"

let string_of_vm prog =
  String.concat "\n" (List.map string_of_decl prog)

(* ==== 仮想機械コードへの変換 ==== *)

let fresh_label = Misc.fresh_id_maker "L"
  
let rec local_vars env = function
  | F.CompExp (F.IfExp (_, e1, e2)) -> local_vars env e1 @ local_vars env e2
  | F.LetExp (id, _, e) -> id :: local_vars env e
  | F.LoopExp (id, _, e) -> id :: local_vars env e
  | _ -> []

let rec trans_val env = function
  | F.Var i -> (try Environment.lookup i env
                with Environment.Not_bound -> err ("Variable not bound: " ^ i))
  | F.Fun i -> Proc i
  | F.IntV i -> IntV i
and trans_cexp ?loop_label ?loop_var target env = function
  | F.ValExp v ->
     [ Move (target, trans_val env v) ]
  | F.BinOp (op, v1, v2) ->
     [ BinOp (target, op, trans_val env v1, trans_val env v2) ]
  | F.AppExp (v1, vs) ->
     [ Call (target, trans_val env v1, List.map (trans_val env) vs) ]
  | F.IfExp (v, e1, e2) ->
     let l1 = fresh_label "" in
     let l2 = fresh_label "" in
     let v = trans_val env v in
     let insts1 = trans_exp ?loop_label ?loop_var target env e1 in
     let insts2 = trans_exp ?loop_label ?loop_var target env e2 in
     BranchIf (v, l1) ::
       insts2 @ (* if v is false *)
       [ Goto l2 ] @ (* -- *)
         [ Label l1 ] @ (* if v is true *)
           insts1 @
             [ Label l2 ] (* -- *)
  | F.TupleExp vs ->
     [ Malloc (target, List.map (trans_val env) vs) ]
  | F.ProjExp (v, i) ->
     [ Read (target, trans_val env v, i) ]
and trans_exp ?loop_label ?loop_var target env = function
  | F.CompExp c -> trans_cexp ?loop_label ?loop_var target env c
  | F.LetExp (id, e1, e2) ->
     let id' = match Environment.lookup id env with
       | Local id' -> id'
       | _         -> err "Unexpected error" in
     let insts1 = trans_cexp id' env e1 in
     let insts2 = trans_exp ?loop_label ?loop_var target env e2 in
     insts1 @ insts2
  | F.LoopExp (id, e1, e2) ->
     let id' = match Environment.lookup id env with
         Local id -> id
       | _        -> err "Unexpected error" in
     let insts1 = trans_cexp id' env e1 in
     let label = fresh_label "" in
     let insts2 = trans_exp ~loop_label:label ~loop_var:id' target env e2 in
     insts1 @ [Label label] @ insts2
  | F.RecurExp v ->
     (match loop_label, loop_var with
        Some loop_label, Some loop_var -> [ Move (loop_var, trans_val env v); Goto loop_label ]
      | _ -> err "recur expression must be in loop expression")
     
let trans_decl (F.RecDecl (proc_name, params, body)) =
  let env = (* 引数に Param * を対応させる (0-based) *)
    List.mapi (fun i p -> (i, p)) params
    |> List.fold_left (fun env (i, param) ->
           Environment.extend param (Param i) env) Environment.empty in
  let local_vars = local_vars env body in  
  let env = (* ローカル変数に Local * を対応させる (1-indexed, Local 0 は戻り値用) *)
    List.mapi (fun i l -> (i + 1, l)) local_vars
    |> List.fold_left (fun env (i, local) ->
           Environment.extend local (Local i) env) env in
  (* 関数宣言を変換してできる命令列 = body の実行結果を Local 0 に格納する命令列 + Local 0 を返す命令 *)
  let insts = trans_exp 0 env body @ [Return (Local 0)] in
  ProcDecl (proc_name, List.length local_vars + 1, insts)

(* entry point *)
let trans = List.map trans_decl
