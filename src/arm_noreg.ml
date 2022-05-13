module S = Syntax
open Arm_spec

exception Error of string
let err s = raise (Error s)

(* ==== メモリアクセス関連 ==== *)

(* 「reg中のアドレスからoffsetワード目」をあらわすaddr *)
let mem_access reg offset = RI (reg, offset * 4)

let local_access i = mem_access Fp (-i-2)

(* Vm.Param は 0 から数えるものと仮定 *)
let param_to_reg = function
    0 -> A1
  | 1 -> A2
  | i -> err ("invalid parameter: " ^ string_of_int i)

(* Vm.operandから値を取得し，レジスタrdに格納するような
   stmt listを生成 *)
let gen_operand rd = function
    Vm.Param i ->
      let rs = param_to_reg i in
      if rd = rs then [] else [Instr (Mov (rd, (R rs)))]
  | Vm.Local i -> [Instr (Ldr (rd, local_access i))]
  | Vm.Proc  lbl -> [Instr (Ldr (rd, L lbl))]
  | Vm.IntV  i -> [Instr (Mov (rd, I i))]

(* ==== 仮想マシンコード --> アセンブリコード ==== *)

let fresh_label = Vm.fresh_label

let gen_instr name = function
  | Vm.Move (ofs, op) ->
     gen_operand V1 op @ [Instr (Str (V1, local_access ofs))]
  | Vm.BinOp (ofs, bop, op1, op2) ->
     let bop_instrs = match bop with
       | S.Plus -> [Instr (Add (V1, V1, R V2))]
       | S.Mult -> [Instr (Mul (V1, V1, V2))]
       | S.Lt -> let l1 = fresh_label "" in
                 let l2 = fresh_label "" in
                 [ Instr (Cmp (V1, R V2));
                   Instr (Blt l1);
                   Instr (Mov (V1, I 0)); (* if l1 >= l2 *)
                   Instr (B l2);
                   Label l1;
                   Instr (Mov (V1, I 1)); (* if l1 < l2 *)
                   Label l2
                 ] in
     gen_operand V1 op1 @ gen_operand V2 op2 @ bop_instrs @ [Instr (Str (V1, local_access ofs))]
  | Vm.Label lbl -> [Label lbl]
  | Vm.BranchIf (op, lbl) ->
     gen_operand V1 op @ [Instr (Cmp (V1, I 0)); Instr (Bne lbl)]
  | Vm.Goto lbl -> [Instr (B lbl)]
  | Vm.Call (ofs, op_f, op1 :: op2 :: _) ->
     [Instr (Str (A1, mem_access Sp 0)); (* a1, a2 レジスタの値の退避 *)
      Instr (Str (A2, mem_access Sp 1))] @
       gen_operand A1 op1 @ (* a1, a2 <- op1, op2 *)
         gen_operand A2 op2 @
           gen_operand V1 op_f @ (* v1 <- op_f *)
             [Instr (Blx V1);
              Instr (Str (A1, local_access ofs)); (* ofs <- a1 *)
              Instr (Ldr (A1, mem_access Sp 0)); (* saved a1, a2 を戻す *)
              Instr (Ldr (A2, mem_access Sp 1))]
  | Vm.Return op ->
     gen_operand A1 op @ [Instr (B (name ^ "_ret"))]
  | Vm.Malloc (ofs, ops) ->
     let instrs =
       List.mapi (fun i op -> (i, op)) ops
       |> (fun l -> List.fold_right (fun (i, op) instrs ->
                        Instr (Ldr (V1, local_access ofs)) :: gen_operand V2 op @ [Instr (Str (V2, mem_access V1 i))] @ instrs) l []) in
     [Instr (Str (A1, mem_access Sp 0)); (* a1, a2 レジスタの退避 *)
      Instr (Str (A2, mem_access Sp 1));
      Instr (Mov (A1, I (List.length ops))); (* 確保するワード数を指定 *)
      Instr (Bl "mymalloc"); (* メモリ領域の確保 *)
      Instr (Str (A1, local_access ofs)); (* ofs <- 先頭アドレス *)
      Instr (Ldr (A1, mem_access Sp 0)); (* saved a1, a2 を戻す *)
      Instr (Ldr (A2, mem_access Sp 1))
] @ instrs
  | Vm.Read (ofs, op, i) ->
     gen_operand V1 op @
       [Instr (Ldr (V1, mem_access V1 i));
        Instr (Str (V1, local_access ofs))]
  | _ -> err "Not Implemented"
(* V.decl -> loc list *)
let gen_decl (Vm.ProcDecl (name, nlocal, instrs)) =
  [Dir (D_align 2);
   Dir (D_global name);
   Label name;
   Instr (Str (Fp, mem_access Sp (-1))); (* fp, lr レジスタの値の退避 *)
   Instr (Str (Lr, mem_access Sp (-2)));
   Instr (Sub (Fp, Sp, I 4)); (* fp レジスタを下げる *)
   Instr (Sub (Sp, Sp, I ((nlocal + 4) * 4)))] @ (* sp レジスタを下げる．+4 は saved fp, lr, saved a1, a2 の分 *)
    List.fold_right (fun instr instrs ->
        gen_instr name instr @ instrs) instrs [] @
      [Label (name ^ "_ret");
       Instr (Add (Sp, Fp, I 4)); (* sp レジスタを戻す *)
       Instr (Ldr (Fp, mem_access Sp (-1))); (* fp, lr レジスタを戻す *)
       Instr (Ldr (Lr, mem_access Sp (-2)));
       Instr (Bx Lr)] (* 呼び出し元に戻す *)

(* entry point: Vm.decl list -> stmt list *)
let codegen vmprog =
  Dir D_text :: List.concat (List.map gen_decl vmprog)
