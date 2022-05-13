module Map = MyMap
module Set = MySet

type 'a t = ('a, 'a Set.t) Map.t

let empty = Map.empty

let vertices g = List.map (fun (v, _) -> v) (Map.to_list g) |> Set.from_list

let neighbors v g = match Map.get v g with
    Some vs -> vs
  | None -> Set.empty
  
let complete vs =
  let vs' = Set.to_list vs in
  List.fold_left (fun g v -> Map.assoc v (Set.remove v vs) g) empty vs'
    
let merge g1 g2 =
  List.fold_left (fun g (k, v) ->
      match Map.get k g with
        Some v' -> Map.assoc k (Set.union v v') g
      | None    -> Map.assoc k v g) g2 (Map.to_list g1)
