module Set = MySet
module Map = MyMap
module G = Graph

exception Error of string
let err s = raise (Error s)

type binOp = Vm.binOp

type offset = int
type label = string

type reg = int       (* 汎用レジスタ．0以上の整数 *)

(* コード生成が swap に利用するための専用レジスタ．
   実際にどの物理レジスタを用いるかはアーキテクチャ依存 *)
let reserved_reg = -1
                 
type dest =
    R of reg     (* レジスタ *)
  | L of offset  (* 局所領域の関数フレーム中の相対位置  *)

type operand =
    Param of int
  | Reg   of reg
  | Proc  of label
  | IntV  of int
  | Local of int (* malloc 用 *)

type instr =
    Move     of reg * operand
  | Load     of reg * offset
  | Store    of reg * offset
  | BinOp    of reg * Vm.binOp * operand * operand
  | Label    of label
  | BranchIf of operand * label
  | Goto     of label
  | Call     of dest * operand * operand list
  | Return   of operand
  | Malloc   of dest * operand list
  | Read     of dest * operand * int

type decl =
    ProcDecl of label * int * instr list (* int: 局所領域の個数 *)

type prog = decl list


(* Formatter *)

let string_of_binop = function
    Syntax.Plus -> "add"
  | Syntax.Mult -> "mul"
  | Syntax.Lt   -> "lt"

let string_of_dest = function
    R r -> "r" ^ string_of_int r
  | L oft -> "t" ^ string_of_int oft

let string_of_operand = function
    Param i -> "p" ^ string_of_int i
  | Reg r -> "r" ^ string_of_int r
  | Proc  l -> l
  | IntV  i -> string_of_int i
  | Local o -> "t" ^ string_of_int o             

let string_of_instr idt tab = function
    Move (t, v) ->
      idt ^ "move" ^ tab ^ "r" ^ string_of_int t ^ ", " ^
      string_of_operand v
  | Load (r, oft) ->
      idt ^ "load" ^ tab ^ "r" ^ string_of_int r ^ ", t" ^
      string_of_int oft
  | Store (r, oft) ->
      idt ^ "store" ^ tab ^ "r" ^ string_of_int r ^ ", t" ^
      string_of_int oft
  | BinOp (t, op, v1, v2) ->
      idt ^ string_of_binop op ^ tab ^ "r" ^ string_of_int t ^ ", " ^
      string_of_operand v1 ^ ", " ^ string_of_operand v2
  | Label lbl -> lbl ^ ":"
  | BranchIf (v, lbl) ->
      idt ^ "bif" ^ tab ^ string_of_operand v ^ ", " ^ lbl
  | Goto lbl ->
      idt ^ "goto" ^ tab ^ lbl
  | Call (dst, tgt, [a0; a1]) ->
      idt ^ "call" ^ tab ^ string_of_dest dst ^ ", " ^
      string_of_operand tgt ^
      "(" ^ string_of_operand a0 ^ ", " ^ string_of_operand a1 ^ ")"
  | Call (_, _, args) -> err ("Illegal number of arguments: " ^
                              string_of_int (List.length args))
  | Return v ->
      idt ^ "ret" ^ tab ^ string_of_operand v
  | Malloc (t, vs) ->
      idt ^ "new" ^ tab ^ string_of_dest t ^ " [" ^
      (String.concat ", " (List.map string_of_operand vs)) ^ "]"
  | Read (t, v, i) ->
      idt ^ "read" ^ tab ^ string_of_dest t ^ " #" ^
      string_of_int i ^ "(" ^ string_of_operand v ^ ")"

let string_of_decl (ProcDecl (lbl, n, instrs)) =
  "proc " ^ lbl ^ "(" ^ string_of_int n ^ ") =\n" ^
  (String.concat "\n"
     (List.map (fun i -> string_of_instr "  " "\t" i) instrs)) ^ "\n"

let string_of_reg prog =
  String.concat "\n" (List.map string_of_decl prog)

(* ==== レジスタ割付け ==== *)

let interference_graph lives instrs =
  instrs
  |> List.map (fun ((i, r) as instr) ->                    
         let l1 = match Map.get instr lives.Dfa.before with
             Some l -> l
           | None -> Set.empty in
         let l1 = Set.remove Live.dummy l1 in
         let l2 = match Map.get instr lives.Dfa.after with
             Some l -> l
           | None -> Set.empty in
         let l2 = Set.remove Live.dummy l2 in
         let g1 = G.complete l1 in
         let g2 = G.complete l2 in
         G.merge g1 g2)
  |> List.fold_left G.merge G.empty

let enum_to n =
  let rec f m = if m < n then Set.insert m (f (m + 1)) else Set.empty
  in f 0

let rec combine l1 l2 = match l1, l2 with
    [], _ -> []
  | _, [] -> []
  | x :: l1, y :: l2 -> (x, y) :: combine l1 l2

(* ops 内の local の値をレジスタに格納する．
   戻り値: (reg_allocs', pre, post)
   reg_allocs': reg_allocs + 「ops 内の local とその値を格納するレジスタの対応関係」
   pre: ops 内の local の値をレジスタに格納する命令 + 汎用レジスタの値の退避命令
   post: 汎用レジスタの値の復帰命令
   注意: 汎用レジスタの値を正しく復帰するために，pre と post の命令は両方実行される必要がある． *)
let transfer_operands ops nreg nlocal reg_allocs =
  let locals = List.flatten (List.map (fun op ->
    match op with
      Vm.Local i -> (match List.assoc_opt op reg_allocs with
                       Some _ -> []
                     | None -> [i])
    | _ -> []) ops) in
  let used = Set.from_list (List.flatten (List.map (fun op ->
    match op with
      Vm.Local _ -> (match List.assoc_opt op reg_allocs with
                       Some r -> [r]
                     | None -> [])
    | _ -> []) ops)) in
  let unused = Set.to_list (Set.diff (enum_to nreg) used) in
  let corr = combine locals ((-1) :: unused) in
  let pre = List.flatten (List.mapi (fun ofs (i, r) -> if r <> -1 then [Store (r, nlocal + ofs); Load (r, i)] else [Load (r, i)]) corr) in
  let post = List.flatten (List.mapi (fun ofs (_, r) -> if r <> -1 then [Load (r, nlocal + ofs)] else []) corr) in
  (List.map (fun (i, r) -> (Vm.Local i, r)) corr @ reg_allocs, pre, post)

(* ofs <- op に対応する命令を生成する *)
let transfer ofs op reg_allocs = match List.assoc_opt (Vm.Local ofs) reg_allocs with
    Some r -> (match op with
                Vm.Param i -> [Move (r, Param i)]
              | Vm.Local i -> (match List.assoc_opt op reg_allocs with
                                 Some r' -> [Move (r, Reg r')]
                               | None -> [Load (r, i)])
              | Vm.Proc lbl -> [Move (r, Proc lbl)]
              | Vm.IntV i -> [Move (r, IntV i)])
  | None -> (match op with
                    Vm.Param i -> [Move (reserved_reg, Param i);
                                   Store (reserved_reg, ofs)]
                  | Vm.Local i -> (match List.assoc_opt op reg_allocs with
                                     Some r -> [Store (r, ofs)]
                                   | None -> [Load (reserved_reg, i);
                                              Store (reserved_reg, ofs)])
                  | Vm.Proc lbl -> [Move (reserved_reg, Proc lbl);
                                    Store (reserved_reg, ofs)]
                  | Vm.IntV i -> [Move (reserved_reg, IntV i);
                                  Store (reserved_reg, ofs)])

let trans_operand op reg_allocs =
  match op with
    Vm.Param i -> Param i
  | Vm.Local i -> (match List.assoc_opt op reg_allocs with
                     Some r -> Reg r
                   | None -> Local i)
  | Vm.Proc lbl -> Proc lbl
  | Vm.IntV i -> IntV i

let trans_instr nreg nlocal reg_allocs = function
  | Vm.Move (ofs, op) -> transfer ofs op reg_allocs
  | Vm.BinOp (ofs, bop, op1, op2) ->
     let (reg_allocs', pre, post) = transfer_operands [op1; op2] nreg nlocal reg_allocs in
     let op1 = trans_operand op1 reg_allocs' in
     let op2 = trans_operand op2 reg_allocs' in
     pre @ [BinOp (reserved_reg, bop, op1, op2)] @ post @
       (match List.assoc_opt (Vm.Local ofs) reg_allocs with
          Some r -> [Move (r, Reg reserved_reg)]
        | None -> [Store (reserved_reg, ofs)])
  | Vm.Label lbl -> [Label lbl]
  | Vm.BranchIf (op, lbl) ->
     (* op に割り当てられうるレジスタは -1 のみなので，post = [] *)
     let (reg_allocs, pre, _) = transfer_operands [op] nreg nlocal reg_allocs in
     let op = trans_operand op reg_allocs in
     pre @ [BranchIf (op, lbl)]
  | Vm.Goto lbl -> [Goto lbl]
  | Vm.Call (ofs, opf, [op1; op2]) ->   
     let (reg_allocs', pre, post) = transfer_operands [opf; op1; op2] nreg nlocal reg_allocs in
     let opf = trans_operand opf reg_allocs' in
     let op1 = trans_operand op1 reg_allocs' in
     let op2 = trans_operand op2 reg_allocs' in
     pre @ [Call (R reserved_reg, opf, [op1; op2])] @ post @
       (match List.assoc_opt (Vm.Local ofs) reg_allocs with
          Some r -> [Move (r, Reg reserved_reg)]
        | None -> [Store (reserved_reg, ofs)])
  | Vm.Return op ->
     (* op に割り当てられうるレジスタは -1 のみなので，post = [] *)
     let (reg_allocs, pre, _) = transfer_operands [op] nreg nlocal reg_allocs in
     let op = trans_operand op reg_allocs in
     pre @ [Return op]
  | Vm.Malloc (ofs, ops) ->
     let ops = List.map (fun op -> trans_operand op reg_allocs) ops in
     (match List.assoc_opt (Vm.Local ofs) reg_allocs with
        Some r -> [Malloc (R r, ops)]
      | None -> [Malloc (L ofs, ops)])
  | Vm.Read (ofs, op, i) ->
     (* op に割り当てられうるレジスタは -1 のみなので，post = [] *)
     let (reg_allocs', pre, _) = transfer_operands [op] nreg nlocal reg_allocs in
     let op = trans_operand op reg_allocs' in
     pre @ 
       (match List.assoc_opt (Vm.Local ofs) reg_allocs with
          Some r -> [Read (R r, op, i)]
        | None -> [Read (R reserved_reg, op, i); Store (reserved_reg, ofs)])
  | _ -> err "Not implemented"  

(* よくあるレジスタ割当て *)  
let trans_decl nreg lives (Vm.ProcDecl (lbl, nlocal, instrs)) =
  let graph = interference_graph lives (List.mapi (fun r i -> (i, (lbl, r + 1))) instrs) in
  let rec loop rest st spilled = (* simplify, spill を行なう *)
    let p v = Set.size (Set.diff (G.neighbors v graph) (Set.from_list st)) < nreg in
    let (smaller, greater) = List.partition p rest in
    let st = smaller @ st in
    match greater with
      [] -> (st, spilled)
    | v :: rest -> loop rest (v :: st) (v :: spilled) in
  let (st, spilled) = loop (Set.to_list (G.vertices graph)) [] [] in
  (* reg_alloc : (Vm.operand, int) list *)
  let neighbor_regs v reg_alloc =
    G.neighbors v graph
    |> Set.to_list
    |> List.fold_left (fun s v -> match List.assoc_opt v reg_alloc with
                                    Some r -> Set.insert r s
                                  | _ -> s) Set.empty in
  let rec reg_allocate st reg_alloc = match st with
      [] -> reg_alloc
    | v :: st when List.mem v spilled ->
       reg_allocate st reg_alloc
    | v :: st ->
       let unused = Set.diff (enum_to nreg) (neighbor_regs v reg_alloc)
                    |> Set.to_list in
       match unused with
         r :: _ -> reg_allocate st ((v, r) :: reg_alloc)
       | []     -> err "Failed to allocate registers" in
  let reg_alloc = reg_allocate st [] in
  let instrs = List.flatten (List.map (trans_instr nreg nlocal reg_alloc) instrs) in
  ProcDecl (lbl, nlocal + nreg, instrs)

(* entry point *)
let trans nreg lives = List.map (trans_decl nreg lives)
