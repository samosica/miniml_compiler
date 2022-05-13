open Syntax

type exval =
  | IntV of int
  | BoolV of bool
  | TupleV of exval * exval
  | ProcV of id * exp * dnval Environment.t ref
  | RecurV of exval
and dnval = exval

let rec string_of_exval = function
    IntV i -> string_of_int i
  | BoolV b -> string_of_bool b
  | TupleV (v1, v2) -> "(" ^ string_of_exval v1 ^ ", " ^ string_of_exval v2 ^ ")"
  | ProcV _ -> "<fun>"
  | RecurV _ -> err "Unexpected error"
          
let pp_val v = print_string (string_of_exval v)
          
let apply_prim op arg1 arg2 = match op, arg1, arg2 with
    Plus, IntV i1, IntV i2 -> IntV (i1 + i2)
  | Plus, _, _ -> err ("Both arguments must be integer: +")
  | Mult, IntV i1, IntV i2 -> IntV (i1 * i2)
  | Mult, _, _ -> err ("Both arguments must be integer: *")
  | Lt, IntV i1, IntV i2 -> BoolV (i1 < i2)
  | Lt, _, _ -> err ("Both arguments must be integer: <")

let rec eval_exp env exp =
  match exp.exp_desc with
    Var x -> 
     (try Environment.lookup x env
      with 
        Environment.Not_bound -> err ("Variable not bound: " ^ x))
  | ILit i -> IntV i
  | BLit b -> BoolV b
  | BinOp (op, exp1, exp2) -> 
      let arg1 = eval_exp env exp1 in
      let arg2 = eval_exp env exp2 in
      apply_prim op arg1 arg2
  | IfExp (exp1, exp2, exp3) ->
      let test = eval_exp env exp1 in
        (match test with
            BoolV true -> eval_exp env exp2 
          | BoolV false -> eval_exp env exp3
          | _ -> err ("Test expression must be boolean: if"))
  | LetExp (id, _, e1, e2) ->
     let v = eval_exp env e1 in
     let env = Environment.extend id v env in
     eval_exp env e2
  | LetRecExp (id, _, x, e1, e2) ->
     let dummyenv = ref Environment.empty in
     let env = Environment.extend id (ProcV (x, e1, dummyenv)) env in
     dummyenv := env;
     eval_exp env e2
  | FunExp (id, exp) ->
     ProcV (id, exp, ref env)
  | AppExp (exp1, exp2) ->
     let funval = eval_exp env exp1 in
     let arg = eval_exp env exp2 in
     (match funval with
        ProcV (id, body, env) ->
         let env = Environment.extend id arg !env in
         eval_exp env body
      | _ -> err ("Non-function value is applied"))
  | LoopExp (id, _, e1, e2) ->
     let v1 = eval_exp env e1 in
     let env = Environment.extend id v1 env in
     let rec loop env =
       let v2 = eval_exp env e2 in
       (match v2 with
          RecurV v -> let env = Environment.extend id v env
                      in loop env
        | _        -> v2) in
     loop env
  | RecurExp e ->
     RecurV (eval_exp env e)
  | TupleExp (e1, e2) ->
     let el1 = eval_exp env e1 in
     let el2 = eval_exp env e2 in
     TupleV (el1, el2)
  | ProjExp (e, i, _) ->
     let v = eval_exp env e in
     (match v, i with
        TupleV (v1, _), 1 -> v1
      | TupleV (_, v2), 2 -> v2
      | TupleV _      , _ -> err "Index out of bounds"
      | _             , _ -> err "Projection expression must start with tuple")
