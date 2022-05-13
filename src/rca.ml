(* 到達コピー解析 (reaching copy analysis)
 * ある地点におけるプロパティ = その地点に到達可能なコピー命令
 * コピー命令は変数の組で表す
 * 最初に与えるプロパティはプログラムに含まれるすべてのコピー命令とし，
 * ふるい落としていくことで，正しい値を計算する
 *)
open Vm
open Cfg
open Dfa
module Set = MySet
           
let dummy = Move (-1, Local (-1))

let compare left right =
  if Set.is_empty (Set.diff left right) then
    (if Set.is_empty (Set.diff right left) then EQ else GT)
  else
    (if Set.is_empty (Set.diff right left) then LT else NO)

let lub left right = Set.intersect left right

let string_of_instrs = Rda.string_of_instrs

let is_var = function
  | Param _ | Local _ -> true
  | _ -> false

let transfer entry_instrs instr =
  let gen instrs = match instr with
      Move (_, src) when is_var src ->
       Set.insert instr instrs
    | _ -> instrs in
  let kill instrs = match instr with
      Move (dst, _)
    | BinOp (dst, _, _, _)
    | Call (dst, _, _)
    | Malloc (dst, _)
    | Read (dst, _, _) ->
       instrs
       |> Set.to_list
       |> List.filter (fun i -> match i with
              Move (dst', src') -> dst' <> dst && src' <> Local dst
            | _ -> false)
       |> Set.from_list
    | _ -> instrs in
  gen (kill entry_instrs)

let copy_instrs vmcode =
  let p i = match i with
      Move (_, src) -> is_var src
    | _ -> false in
  vmcode
  |> List.map (fun decl -> match decl with
         ProcDecl (_, _, instrs) -> List.filter p instrs)
  |> List.concat
  |> Set.from_list
  
let make vmcode =
  let copy_instrs = copy_instrs vmcode in
  {
    direction = FORWARD;
    transfer = transfer;
    compare = compare;
    lub = lub;
    bottom = Set.insert dummy copy_instrs;
    init = copy_instrs;
    to_str = string_of_instrs
  }
