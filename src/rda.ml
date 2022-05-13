(* 到達定義解析 (reaching definition analysis)
 * ある地点におけるプロパティ = その地点に到達可能な代入命令
 *)
open Vm
open Cfg
open Dfa
module Set = MySet

let dummy = Move (-1, Local (-1)) (* Return (Local (-1)) *)

let bottom = Set.empty

let compare = Live.compare

let lub = Live.lub

let string_of_instrs instrs =
  String.concat "; "
    (List.map (Vm.string_of_instr "" " ")
       (List.filter (fun i -> i <> dummy) (Set.to_list instrs)))

let dst_of_instr = function
    Move (dst, _)
  | BinOp (dst, _, _, _)
  | Call (dst, _, _)
  | Malloc (dst, _)
  | Read (dst, _, _) -> Some dst
  | _ -> None

let transfer entry_instrs instr =
  let gen instrs =
    lub
      (match instr with
         Move _
       | BinOp _
       | Call _
       | Malloc _
       | Read _ -> Set.singleton instr
       | _ -> Set.empty)
      instrs in
  let kill instrs =
    let dst = dst_of_instr instr in
    match dst with
      Some _ ->
       Set.from_list (* instr と同じ destination を持つ代入命令を削除する *)
         (List.filter (fun i -> dst_of_instr i <> dst) (Set.to_list instrs))
    | None -> instrs in
  gen (kill entry_instrs)

let make () = {
    direction = FORWARD;
    transfer = transfer;
    compare = compare;
    lub = lub;
    bottom = bottom;
    init = Set.singleton dummy;
    to_str = string_of_instrs
}
