module YourClientName.Dictionary

// Trie
type Trie

val empty : unit -> Trie

val insert : string -> Trie -> Trie

val lookup : string -> Trie -> bool

val step : char -> Trie -> (bool * Trie) option

