open Vm

type vm_state = {
  stack : (operand list) list;
  heap  : (operand list) list;
  pc : (label * int * int) list;
  prog : prog;
  running : bool;
}

let string_of_pc pc =
  let (label, i, tgt) = pc in
  label ^ ":" ^ string_of_int i
    ^ "->" ^ string_of_int tgt ^ ", "

let string_of_state state =
  "Running :" ^ string_of_bool state.running ^ "\n" ^
  "Stack :\n" ^
  List.fold_left (fun res st ->
    res ^ fst (List.fold_left (fun (res, i) v ->
      ((res ^ string_of_operand v ^ ", " ^
      if i mod 10 = 1 then "\n" else ""), i + 1)
    ) ("", 0) st) ^ "|\n"
  ) "" state.stack ^
  "Heap :\n" ^
  List.fold_left (fun res st ->
    res ^ List.fold_left (fun res v ->
      res ^ string_of_operand v ^ ", "
    ) "" st ^ "|\n"
  ) "" state.heap ^
  "PCs :\n" ^
  List.fold_left (fun res pc -> res ^ string_of_pc pc
  ) "" state.pc

let rec list_init n v = match n with
    0 -> []
  | k -> v :: (list_init (k - 1) v)

let getl n src = List.nth src n
let setl n src v =
  List.mapi (fun i x -> if i = n then v else x) src

let getv state src = match src with
    Param p -> getl p (List.hd state.stack)
  | Local l -> getl (l + 2) (List.hd state.stack)
  | _       -> src

let setv state tgt v =
  {state with
    stack = setl (tgt + 2) (List.hd state.stack) v
              :: List.tl state.stack
  }

let push_stack state size =
  {state with
    stack = (list_init (size + 2) (IntV (-42))) :: state.stack
  }

let pop_stack state =
  {state with
    stack = List.tl state.stack
  }

let push_heap state size =
  let res = {state with
    heap = (list_init size (IntV (-42))) :: state.heap
  } in
  (IntV (List.length res.heap - 1), res)

let heap_pos state (IntV p) =
  List.length state.heap - p - 1

let heap_get state p i =
  getl i ( getl (heap_pos state p) state.heap )

let heap_set state p i v =
  let hp = heap_pos state p in
  {state with
    heap = setl hp state.heap (setl i (getl hp state.heap) v)
  }

let push_pc state pc =
  {state with
    pc = pc :: state.pc
  }

let top_pc state = List.hd state.pc

let pop_pc state =
  {state with
    pc = List.tl state.pc
  }

let set_pc state pc =
  push_pc (pop_pc state) pc

let empty_pc state =
  List.length state.pc = 1

let next state =
  let (label, pc, tgt) = top_pc state in
  set_pc state (label, pc + 1, tgt)

let endvm state =
  {state with
    running = false
  }

let get_decl state label = 
  print_string label;
  List.find (fun (ProcDecl (l, x, instr)) -> label = l) state.prog
 
let get_instr state =
  let (label, pc, tgt) = top_pc state in
  let ProcDecl (_,_,instr) = get_decl state label in
  List.nth instr pc

let local_vars state label =
  let ProcDecl (_,x,_) = get_decl state label in x

let jump state label =
  let (fn, pc, tgt) = top_pc state in
  let ProcDecl (fn, x, instr) = get_decl state fn in
  let (_, num) = List.find (fun (ins, i) ->
    match ins with Label k -> k = label | _ -> false) 
    (List.mapi (fun i x -> (x, i)) instr) in
    set_pc state (fn, num, tgt)

let run_instr state instr = match instr with
    Move (tgt, src) ->
      next (setv state tgt (getv state src))
  | BinOp (tgt, op, src1, src2) ->
      let (IntV v1) = getv state src1 in
      let (IntV v2) = getv state src2 in
      let res = (match op with
        Syntax.Plus -> v1 + v2
      | Syntax.Mult -> v1 * v2
      | Syntax.Lt   -> if v1 < v2 then 1 else 0) in
      next (setv state tgt (IntV res))
  | Label l -> next state
  | BranchIf (cmp, l) -> 
    let IntV v = getv state cmp in
    if 0 < v then jump state l else next state
  | Goto l -> jump state l
  | Call (tgt, src1, [src2; src3]) ->
     let Proc l = getv state src1 in
     let v2 = getv state src2 in
     let v3 = getv state src3 in
     let size = local_vars state l in
     let state = next state in
     let state = push_stack state size in
     let state = setv state (-2) v2 in
     let state = setv state (-1) v3 in
     push_pc state (l, 0, tgt)
  | Return src1 ->
     let res = getv state src1 in
     let (label, l, tgt) = top_pc state in
     let state = pop_pc state in
     let state = pop_stack state in
     let state = setv state tgt res in
     if empty_pc state then endvm state else state
  | Malloc (tgt, srcs) ->
     let (res, state) = push_heap state (List.length srcs) in
     let (state, _) = List.fold_left (fun (state, i) src -> 
       (heap_set state res i (getv state src), i + 1)
     ) (state, 0) srcs in
     next (setv state tgt res)
  | Read (tgt, src, id) ->
     let v = getv state src in
     next (setv state tgt (heap_get state v id))

let init_vm prog =
  let state = {
    stack = [];
    heap = [];
    pc = [("_toplevel", 0, 0); ("_init", 0, 0)];
    prog = prog;
    running = true;
  } in
  { state with
    stack = [
      ([IntV (-1024); IntV (-1025)] @
        list_init (local_vars state "_toplevel") (IntV (-1026)));
      [IntV (-1027); IntV (-1028); IntV (-1029)]];
  }

let rec run_vm state =
  if state.running then
    let instr = get_instr state in
    print_endline ("\n>>>> " ^
      string_of_pc (List.hd state.pc) ^ ": " ^
      Vm.string_of_instr " " " " instr);
      print_endline (string_of_state state);
    let state = run_instr state instr in
    run_vm state
  else
    state

let run prog =
  run_vm (init_vm prog)
