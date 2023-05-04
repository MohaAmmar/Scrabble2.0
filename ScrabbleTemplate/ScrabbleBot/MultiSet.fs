// Insert your MultiSet.fs file here. All modules must be internal

module internal MultiSet

    type MultiSet<'a when 'a : comparison> = M of Map<'a,uint32>
    let empty = M(Map.empty)
    let isEmpty (M s) = Map.isEmpty s
    let size (M s) = Map.foldBack (fun _ acc i-> acc+i) s (uint32 0)
    let contains a (M s) = s.ContainsKey a
    let rec numItems (a:'a) (M s: MultiSet<'a>) = if Map.tryFind a s = None
                                                  then 0u
                                                  else Map.find a s
    let add (a:'a) (n:uint32) (M s) = if Map.tryFind a s = None
                                      then M (s |> Map.add a n)
                                      else M (s |> Map.add a (s.Item a + n))
    let addSingle (a:'a) (M s) = add a 1u (M s)
    let rec remove (a:'a) (n:uint32) (M s) = if Map.tryFind a s = None
                                             then M s
                                             else if n < s.Item a
                                                 then M (Map.add a ((s.Item a) - n) s)
                                             else M(s.Remove a)
    let removeSingle (a:'a) (M s) = remove a 1u (M s)
    let fold f a (M s) = Map.fold f a s
    let foldBack f (M s) b = Map.foldBack f s b
    let rec ofList (lst:'a list) =
        match lst with
        | [] -> empty
        | x::xs -> add x 1u (ofList xs)
    let rec toList (M s) = Map.foldBack (fun a acc xs -> List.replicate (int acc) a @ xs) s [] 
    let map f (M s) = let (M ms) = empty
                      Map.foldBack (fun a -> add <| (f a)) s (M ms)
    let union (M s1) (M s2) =
         let s3 = empty
         Map.fold (fun acc a i1 ->
            match Map.tryFind a s2 with
            |Some i2 -> if i2 > i1
                         then add a i2 acc
                         else add a i1 acc
            |None -> acc
         ) s3 s1
    let sum (M s1) (M s2) =
         let s3 = empty
         Map.fold (fun acc a i1 ->
            match Map.tryFind a s2 with
            |Some i2 ->  add a (i2 + i1) acc
            |None -> acc
         ) s3 s1
    let subtract (M s1) (M s2) =
         let s3 = M s1
         Map.fold (fun acc a i1 ->
            match Map.tryFind a s2 with
            |Some i2 ->  remove a i2 acc
            |None -> acc 
         ) s3 s1
    let intersection (M s1) (M s2) =
         let s3 = empty
         Map.fold (fun acc a i1 ->
            match Map.tryFind a s2 with
            |Some i2 ->  add a i2 acc
            |None -> acc 
         ) s3 s1
