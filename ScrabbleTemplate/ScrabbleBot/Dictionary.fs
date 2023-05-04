module YourClientName.Dictionary

type Trie =
    | Leaf of bool
    | Node of bool * Map<char, Trie>

let empty () = Leaf false
let insert (s : string) (t : Trie) =
    let rec insertion (s : string) (tree : Trie) : Trie =
        match tree with
        | Leaf _           when (s.Length = 0)   -> Leaf true
        | Node (_ , d)     when (s.Length = 0)   -> Node (true, d)
        
        | Leaf b                            ->
            Node(b, (Map.add s.[0] (insertion (s.Remove (0, 1)) (empty ())) Map.empty ) )
        | Node (b, m)                            ->
            match Map.tryFind s.[0] m with
            // if we find a trie with the char s.[0] then we will overwrite the node with a new node, keep the boolean but insert the rest of the word within the submap of that node, including the char
            | Some v        -> Node(b, (Map.add s.[0] (insertion (s.Remove (0, 1)) v) m))
            // if the char does not exist within the node map, we need to add it and continue the subtrie
            | None          -> Node(b, (Map.add s.[0] (insertion (s.Remove (0, 1)) (empty ())) m)) 
    insertion s t
    
let lookup (word : string) (tree : Trie) =
    let rec look (s : string) t =
        match t with
        | Leaf b       when (s.Length = 0)     -> b // when we at the end of the tree AND at the end of the word - return weather it is a word
        | Leaf _                                    -> false // at the end of the tree, but there is still more letters in the word
        | Node (b, _)       when (s.Length = 0)     -> b // we at end of the word mid-tree, then bool says weather the subtree creates a word
        | Node (_, m)                               ->
            match m.TryFind s.[0] with
            | Some v    -> look (s.Remove (0, 1)) v
            | None      -> false
    look word tree
    
let step (character : char) (tree : Trie) =
    match tree with
    | Leaf _        -> None
    | Node (b, m)   ->
        match (m.TryFind character) with
        | Some v        -> Some (b, v)
        | None          -> None
        
