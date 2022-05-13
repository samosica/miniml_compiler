open Arm_spec

type addr = int

exception UninitializedMemory of addr
exception UninitializedStack of addr
exception UnallocatedHeap of addr
exception SegmentationFault of addr
exception ImplementationError

module type BaseAddr = sig val value : addr end
module StackBaseAddr : BaseAddr = struct let value = max_int end
module HeapBaseAddr : BaseAddr = struct let value = min_int end

module type Memory = sig
  type memval
  type memory
  val base_address : addr
  val abs_address : addr -> addr
  val length : memory -> addr
  val make : addr -> memory
  val get : memory -> addr -> int
  val set : memory -> addr -> int -> memory
  val extend : memory -> addr -> memory
  val fold_left : ('a -> memval -> 'a) -> 'a -> memory -> 'a
  val to_string : memory -> string
end

module Make_Memory (B : BaseAddr) : Memory =
struct
  type memval = int option
  type memory = memval array
  let base_address = B.value
  let abs_address addr = abs (base_address - addr)
  let calc_index addr = abs_address addr / 4
  let make addr = Array.make (addr / 4) None
  let length memory = Array.length memory * 4
  let get memory addr =
    match Array.get memory (calc_index addr) with
    | Some n -> n
    | None -> raise (UninitializedMemory addr)
  let set memory addr v = Array.set memory (calc_index addr) (Some v); memory
  let extend memory addr = Array.append memory (Array.make (addr / 4) None)
  let fold_left = Array.fold_left
  let to_string =
    let string_of_option = function
      | Some n -> string_of_int n
      | None   -> "undef" in
    Array.fold_left (fun acc v -> acc ^ (string_of_option v) ^ "\n") ""
end

module StackMemory : Memory = Make_Memory(StackBaseAddr)
module Stack = struct
  type stack = StackMemory.memory
  let make = StackMemory.make
  let load stack addr =
    let addr' = StackMemory.abs_address addr in
    if 0 <= addr' && addr' < StackMemory.length stack
    then StackMemory.get stack addr
    else raise (UninitializedStack addr)
  let store stack addr v =
    let addr' = StackMemory.abs_address addr in
    let stack = (if StackMemory.length stack <= addr'
                 then StackMemory.extend stack (addr' - StackMemory.length stack + 4)
                 else stack) in
    StackMemory.set stack addr v
  let to_string = StackMemory.to_string
end

module HeapMemory : Memory = Make_Memory(HeapBaseAddr)
module Heap = struct
  type heap = HeapMemory.memory
  let make = HeapMemory.make
  let load heap addr =
    let addr' = HeapMemory.abs_address addr in
    if 0 <= addr' && addr' < HeapMemory.length heap
    then HeapMemory.get heap addr
    else raise (UnallocatedHeap addr)
  let store heap addr v =
    let addr' = HeapMemory.abs_address addr in
    if 0 <= addr' && addr' < HeapMemory.length heap
    then HeapMemory.set heap addr v
    else raise (SegmentationFault addr)
  let tail_address heap = HeapMemory.base_address + HeapMemory.length heap
  let malloc heap addr = HeapMemory.extend heap addr
  let to_string = HeapMemory.to_string
end

type reg_file = (reg * int) list
type label_table = (label * int) list

exception UndefinedLabel of label
exception IllegalRegister of reg

type machine_state = {
   reg_file : reg_file;
   stack : Stack.stack;
   heap : Heap.heap;
   cond_n : bool;
   cond_z : bool;
   label_table : label_table;
   pc : int;
 }

let get_reg_val state reg =
  (match List.assoc_opt reg state.reg_file with
   | None -> raise (IllegalRegister reg)
   | Some n -> n)

let get_mem_val state addr =
  if addr >= 0
  then Stack.load state.stack addr
  else Heap.load state.heap addr

let get_label_val state l =
  (match List.assoc_opt l state.label_table with
   | None -> raise (UndefinedLabel l)
   | Some n -> n)

let get_addr_val state = function
  | I i -> i
  | R r -> get_reg_val state r
  | RI (r, i) -> (get_reg_val state r) + i
  | L l -> get_label_val state l

let get_A1 state = get_reg_val state A1

let set_reg_val state reg v =
  let rec update l k v = (match l with
     | [] -> []
     | (k', v') :: l' -> if k = k' then (k, v) :: l' else (k', v') :: (update l' k v))
  in { state with reg_file = update state.reg_file reg v }

let set_mem_val state addr v =
  if addr >= 0
  then { state with stack = Stack.store state.stack addr v }
  else { state with heap = Heap.store state.heap addr v }

let rec fetch_instr stmts addr =
  if addr = 0 then stmts else fetch_instr (List.tl stmts) (addr-1)

let inc_pc state = { state with pc = state.pc + 1 }

let set_pc state n = { state with pc = n }

let analyze_label =
  let f (tbl, n, stmts) = function
    | Dir _ -> (tbl, n, stmts)
    | Label l -> ((l, n) :: tbl, n, stmts)
    | Instr i -> (tbl, n+1, stmts @ [Instr i])
  in List.fold_left f ([], 0, [])

let run all_stmts initial_state =
  let rec step state = function
    | [] -> state
    | (Instr instr) :: rest ->
      (match instr with
       | Add (r1, r2, addr) ->
         let r2_val = get_reg_val state r2 in
         let addr_val = get_addr_val state addr in
         step (inc_pc (set_reg_val state r1 (r2_val + addr_val))) rest
       | B l -> let (state,  rest) = jump state l in step state rest
       | Bl l ->
         let state = set_reg_val state Lr (state.pc + 1) in
         let (state, rest) = jump state l in
         step state rest
       | Blt l ->
         if state.cond_n
         then let (state, rest) = jump state l in step state rest
         else step (inc_pc state) rest
       | Blx r ->
         let state = set_reg_val state Lr (state.pc + 1) in
         let r_val = get_reg_val state r in
         step (set_pc state r_val) (fetch_instr all_stmts r_val)
       | Bne l ->
         if not state.cond_z
         then let (state, rest) = jump state l in step state rest
         else step (inc_pc state) rest
       | Bx r ->
         let r_val = get_reg_val state r in
         step (set_pc state r_val) (fetch_instr all_stmts r_val)
       | Cmp (r, addr) ->
         let sub = (get_reg_val state r) - (get_addr_val state addr) in
         let cond_n = sub < 0 in
         let cond_z = sub = 0 in
         step (inc_pc { state with cond_n = cond_n; cond_z = cond_z }) rest
       | Ldr (r, addr) ->
         let mem_val = (match addr with
          | I i -> i
          | R r -> get_mem_val state (get_reg_val state r)
          | RI (r, i) -> get_mem_val state ((get_reg_val state r) + i)
          | L l -> get_label_val state l) in
         step (inc_pc (set_reg_val state r mem_val)) rest
       | Mov (r, addr) -> step (inc_pc (set_reg_val state r (get_addr_val state addr))) rest
       | Mul (r1, r2, r3) ->
         let r2_val = get_reg_val state r2 in
         let r3_val = get_reg_val state r3 in
         step (inc_pc (set_reg_val state r1 (r2_val * r3_val))) rest
       | Str (r, addr) ->
         let r_val = get_reg_val state r in
         let address = get_addr_val state addr in
         step (inc_pc (set_mem_val state address r_val)) rest
       | Sub (r1, r2, addr) ->
         let r2_val = get_reg_val state r2 in
         let addr_val = get_addr_val state addr in
         step (inc_pc (set_reg_val state r1 (r2_val - addr_val))) rest)
    | _ -> raise ImplementationError
  and jump state l =
    if l = "_toplevel_ret" then (state, []) else
    if l = "mymalloc"
    then
      let a1_val = get_reg_val state A1 in
      let ret_val = Heap.tail_address state.heap in
      let pc = get_reg_val state Lr in
      let state = { state with heap = Heap.malloc state.heap (a1_val * 4)} in
      let state = set_reg_val state A1 ret_val in
      (set_pc state pc, fetch_instr all_stmts pc)
    else
      let pc = get_label_val state l in (set_pc state pc, fetch_instr all_stmts pc) in
  step initial_state (fetch_instr all_stmts initial_state.pc)

let simulate stmts =
  let (tbl, _, stmts) = analyze_label stmts in
  let initial_state = {
    reg_file =
        [(A1, 0); (A2, 0); (A3, 0); (A4, 0);
         (V1, 0); (V2, 0); (V3, 0); (V4, 0); (V5, 0); (V6, 0); (V7, 0);
         (Fp, StackBaseAddr.value); (Ip, 0); (Sp, StackBaseAddr.value); (Lr, 0)];
    stack = Stack.make 0;
    heap = Heap.make 0;
    cond_n = false;
    cond_z = false;
    label_table = tbl;
    pc = 0;
  } in
  run stmts (set_pc initial_state (get_label_val initial_state "_toplevel"))

let string_of_regfile reg_file =
  List.fold_left (fun acc (reg, v) -> acc ^ string_of_reg reg ^ ": " ^ string_of_int v ^ "\n")
                 "" reg_file

let string_of_state state =
  "[Stack]\n" ^ Stack.to_string state.stack ^
  "\n[Heap]\n" ^ Heap.to_string state.heap ^
  "\n[Register file]\n" ^ string_of_regfile state.reg_file
