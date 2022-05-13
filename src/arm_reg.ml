module S = Syntax
open Arm_spec

exception Error of string
let err s = raise (Error s)

(* ==== メモリアクセス関連 ==== *)

(* Reg.reg -> reg *)
let reg_mappings = [
  (Reg.reserved_reg, Ip);
  (0, V1);
  (1, V2);
  (2, V3);
  (3, V4);
  (4, V5);
  (5, V6);
  (6, V7);
]

let reg_of r = List.assoc r reg_mappings

(* 「reg中のアドレスからoffsetワード目」をあらわすaddr *)
let mem_access reg offset = RI (reg, offset*4)

let local_access i = mem_access Fp (-i-2)

let param_to_reg = function
    0 -> A1
  | 1 -> A2
  | i -> err ("invalid parameter: " ^ string_of_int i)

(* Reg.operand から値を取得し，レジスタrdに格納するような
   stmt listを生成 *)
let gen_operand rd = function
    Reg.Param i ->
      let rs = param_to_reg i in
      if rd = rs then [] else [Instr (Mov (rd, R rs))]
  | Reg.Reg r ->
      let rs = reg_of r in
      if rd = rs then [] else [Instr (Mov (rd, R rs))]
  | Reg.Proc lbl -> [Instr (Ldr (rd, L lbl))]
  | Reg.IntV i -> [Instr (Mov (rd, I i))]
  | Reg.Local i ->
     [Instr (Ldr (rd, local_access i))]

(* ==== Regマシンコード --> アセンブリコード ==== *)

let fresh_label = Vm.fresh_label
                
let gen_instr name nlocal = function
  | Reg.Move (reg, op) ->
     gen_operand (reg_of reg) op
  | Reg.Load (reg, ofs) ->
     [Instr (Ldr (reg_of reg, local_access ofs))]
  | Reg.Store (reg, ofs) ->
     [Instr (Str (reg_of reg, local_access ofs))]
  | Reg.BinOp (reg, bop, op1, op2) ->
     let reg = reg_of reg in
     let (r2, esc, ret) =
       if reg = Ip
       then (V1, [Instr (Str (V1, mem_access Sp 2))], [Instr (Ldr (V1, mem_access Sp 2))])
       else (reg, [], []) in
     let bop_instrs = match bop with
       | S.Plus -> [Instr (Add (reg, Ip, R r2))] (* 逆だとダメな例が存在する *)
       | S.Mult -> [Instr (Mul (reg, Ip, r2))]
       | S.Lt -> let l1 = fresh_label "" in
                 let l2 = fresh_label "" in
                 [ Instr (Cmp (Ip, R r2));
                   Instr (Blt l1);
                   Instr (Mov (reg, I 0)); (* if l1 >= l2 *)
                   Instr (B l2);
                   Label l1;
                   Instr (Mov (reg, I 1)); (* if l1 < l2 *)
                   Label l2
                 ] in    
       esc @ gen_operand Ip op1 @ gen_operand r2 op2 @ bop_instrs @ ret
  | Reg.Label lbl -> [Label lbl]
  | Reg.BranchIf (op, lbl) ->
     gen_operand Ip op @ [Instr (Cmp (Ip, I 0)); Instr (Bne lbl)]
  | Reg.Goto lbl -> [Instr (B lbl)]
  | Reg.Call (dest, op_f, [op1; op2]) ->
     let esc = [Instr (Str (A1, mem_access Sp 0)); (* a1, a2 レジスタ，汎用レジスタの値の退避 *)
                Instr (Str (A2, mem_access Sp 1))] @
                 List.map (fun i -> Instr (Str (reg_of i, mem_access Sp (i + 2)))) [0; 1; 2; 3; 4; 5; 6] in
     let ret = [Instr (Ldr (A1, mem_access Sp 0)); (* a1, a2 レジスタ，汎用レジスタを戻す *)
                Instr (Ldr (A2, mem_access Sp 1))] @
                 List.map (fun i -> Instr (Ldr (reg_of i, mem_access Sp (i + 2)))) [0; 1; 2; 3; 4; 5; 6] in
     let instr = match dest with
         Reg.R r -> Instr (Mov (reg_of r, R Ip))
       | Reg.L i -> Instr (Str (Ip, local_access i)) in
     esc @ gen_operand A1 op1 @ gen_operand A2 op2 @ gen_operand Ip op_f @
       [Instr (Blx Ip); Instr (Mov (Ip, R A1))] @
         ret @ [instr]
  | Reg.Return op ->
     gen_operand A1 op @ [Instr (B (name ^ "_ret"))]
  | Reg.Malloc (dest, ops) ->
     let esc = [Instr (Str (A1, mem_access Sp 0)); (* a1, a2 レジスタ，汎用レジスタの値の退避 *)
                Instr (Str (A2, mem_access Sp 1))] @
                 List.map (fun i -> Instr (Str (reg_of i, mem_access Sp (i + 2)))) [0; 1; 2; 3; 4; 5; 6] in
     let ret_a = [Instr (Ldr (A1, mem_access Sp 0)); (* a1, a2 レジスタを元に戻す *)
                  Instr (Ldr (A2, mem_access Sp 1))] in
     let ret_v = List.map (fun i -> Instr (Ldr (reg_of i, mem_access Sp (i + 2)))) [0; 1; 2; 3; 4; 5; 6] in
     let instr = match dest with
         Reg.R r -> Instr (Mov (reg_of r, R Ip))
       | Reg.L i -> Instr (Str (Ip, local_access i)) in
     let instrs =
       List.mapi (fun k op -> (k, op)) ops
       |> (fun l -> List.fold_right (fun (k, op) instrs ->
             let new_instrs = match op with
                 Reg.Reg r ->
                 [Instr (Ldr (V1, mem_access Sp (r + 2)));
                  Instr (Str (V1, mem_access Ip k))]
               | _ -> gen_operand V1 op @ [Instr (Str (V1, mem_access Ip k))] in
             new_instrs @ instrs) l []) in
     esc @ [Instr (Mov (A1, I (List.length ops))); Instr (Bl "mymalloc"); Instr (Mov (Ip, R A1))] @
       ret_a @ instrs @ ret_v @ [instr]
  | Reg.Read (dest, op, i) ->
     let instr = match dest with
         Reg.R r -> Instr (Mov (reg_of r, R Ip))
       | Reg.L i -> Instr (Str (Ip, local_access i)) in
     gen_operand Ip op @
       [Instr (Ldr (Ip, mem_access Ip i)); instr]
  | _ -> err "Not Implemented"

let gen_decl (Reg.ProcDecl (name, nlocal, instrs)) =
  [Dir (D_align 2);
   Dir (D_global name);
   Label name;
   Instr (Str (Fp, mem_access Sp (-1))); (* fp, lr レジスタの値の退避 *)
   Instr (Str (Lr, mem_access Sp (-2)));
   Instr (Sub (Fp, Sp, I 4)); (* fp レジスタを下げる *)
   Instr (Sub (Sp, Sp, I ((nlocal + 11) * 4)))] @ (* sp レジスタを下げる．+4 は saved fp, lr, saved a1, a2, 汎用レジスタ の分 *)
    List.fold_right (fun instr instrs ->
        gen_instr name nlocal instr @ instrs) instrs [] @
      [Dir D_ltorg;
       Label (name ^ "_ret");
       Instr (Add (Sp, Fp, I 4)); (* sp レジスタを戻す *)
       Instr (Ldr (Fp, mem_access Sp (-1))); (* fp, lr レジスタを戻す *)
       Instr (Ldr (Lr, mem_access Sp (-2)));
       Instr (Bx Lr)] (* 呼び出し元に戻す *)

let codegen regprog =
  Dir D_text :: List.concat (List.map gen_decl regprog)
