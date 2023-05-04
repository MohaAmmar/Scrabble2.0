namespace YourClientName

open System.Data
open ScrabbleUtil
open ScrabbleUtil.ServerCommunication

open System.IO

open ScrabbleUtil.DebugPrint

// The RegEx module is only used to parse human input. It is not used for the final product.

module RegEx =
    open System.Text.RegularExpressions

    let (|Regex|_|) pattern input =
        let m = Regex.Match(input, pattern)
        if m.Success then Some(List.tail [ for g in m.Groups -> g.Value ])
        else None

    let parseMove ts =
        let pattern = @"([-]?[0-9]+[ ])([-]?[0-9]+[ ])([0-9]+)([A-Z]{1})([0-9]+)[ ]?" 
        Regex.Matches(ts, pattern) |>
        Seq.cast<Match> |> 
        Seq.map 
            (fun t -> 
                match t.Value with
                | Regex pattern [x; y; id; c; p] ->
                    ((x |> int, y |> int), (id |> uint32, (c |> char, p |> int)))
                | _ -> failwith "Failed (should never happen)") |>
        Seq.toList

module Print =

    let printHand pieces hand =
        hand |>
        MultiSet.fold (fun _ x i -> forcePrint (sprintf "%d -> (%A, %d)\n" x (Map.find x pieces) i)) ()

module State = 
    // Make sure to keep your state localised in this module. It makes your life a whole lot easier.
    // Currently, it only keeps track of your hand, your player numer, your board, and your dictionary,
    // but it could, potentially, keep track of other useful
    // information, such as number of players, player turn, etc.

    type state = {
        board         : Parser.board
        dict          : ScrabbleUtil.Dictionary.Dict
        playerNumber  : uint32
        hand          : MultiSet.MultiSet<uint32>
        bag           : uint32
        boardTiles    : Map<coord, char>
    }

    let mkState b d pn h bag bt = {board = b; dict = d;  playerNumber = pn; hand = h; bag = bag ; boardTiles = bt }

    let board st         = st.board
    let dict st          = st.dict
    let playerNumber st  = st.playerNumber
    let hand st          = st.hand
    let bag st = st.bag    
    let boardTile st = st.boardTiles

        
module Move =
    
    type coord = (int * int)
    type letter = uint32 * char
    type word = List<coord * letter>
    type pieces = Map<uint32,Set<char*int>>
    
    let isBoardEmpty (st: State.state) = Map.count st.boardTiles = 0

    let findWords (st:State.state) (letterId:uint32) (co: coord) (pieces : pieces) = //the cords might be oof
        let mutable updatedDict = st.dict
        let rec aux (dict: Dictionary.Dict) (hand: MultiSet.MultiSet<uint32>) (letters: (coord * letter) list ) (words: word list) =
            //look through hand and add to list of words if we find a word
            MultiSet.fold
                (fun word id v ->
                    Set.fold (fun _ (c,_) -> 
                        match Dictionary.step c dict with
                        | None -> word
                        | Some (true, newDict) ->
                            updatedDict <- newDict
                            aux dict (MultiSet.removeSingle id hand) (letters @ [ co, (id, c) ]) ((((letters) @ [(co,(id, c)) ])) :: word) 
                        | Some (false, newDict) ->
                            updatedDict <- newDict
                            aux dict (MultiSet.removeSingle id hand) (letters @ [ co, (id, c) ]) word
                    ) words (Map.find id pieces)
                )
                words
                hand

        aux updatedDict (MultiSet.removeSingle letterId st.hand) list.Empty 
    
    let goThroughHand (st : State.state) (c: coord) (pieces : Map<uint32,Set<char*int>>) =
        MultiSet.fold (fun acc id _ -> acc @ (findWords st id c pieces [])) List.Empty st.hand
        
    let isTileOccupied (c: coord) (st: State.state) =
        match st.boardTiles.TryFind c with
        | Some v    -> Some v
        | None      -> None
        
        
    let checkReservedCoordPlacement (w : letter list) (gcCoords : coord) (givenTile : letter) (st : State.state) : StateMonad.Result<'a, word>  = 
        let gtX, gtY = gcCoords
        let givenTileChar = (snd givenTile)
        let positionInWord = List.findIndex (fun x -> givenTileChar = (snd x) ) w
        
        let wordListBeforeGC    = w[0..positionInWord-1]
        let wordListAfterGC     = w[positionInWord+1..]
        
        let h1 = (isTileOccupied (gtX-1, gtY) st).IsNone
        let h2 = (isTileOccupied (gtX+1, gtY) st).IsNone
        
        let v1 = (isTileOccupied (gtX, gtY-1) st).IsNone
        let v2 = (isTileOccupied (gtX, gtY+1) st).IsNone
        
        let horizontal = (h1&&h2)
        let vertical = (v1&&v2)
        
        match (horizontal) with
        | true ->
            printfn $"Trying horizontal:"
            let wordListBeforeGC_Coordinates = List.mapi (fun i e ->(((gtX-i-1), gtY), e)) (wordListBeforeGC)
            let wordListAfterGC_Coordinates = List.mapi (fun i e ->(((gtX+i+1), gtY), e)) wordListAfterGC
            printfn $"List before given coordinate {wordListBeforeGC_Coordinates} and after {wordListAfterGC_Coordinates}"

            let wl = wordListBeforeGC_Coordinates@wordListAfterGC_Coordinates
            
            let b = List.fold (fun acc e ->
                match acc with
                | Some v ->
                    printfn $"The tile before {e} is reserved by another tile."
                    acc
                | None -> (isTileOccupied (fst e) st)) None wl
            match b with
            | None ->
                printfn $"The word {wl} can be placed on board."
                StateMonad.Success wl
            | _     -> StateMonad.Failure wl
            
        | false ->
            match (vertical) with
            |true -> 
                printfn $"Trying vertical:"
                let wordListBeforeGC_Coordinates = List.mapi (fun i e ->((gtX, (gtY-i-1)), e)) (List.rev wordListBeforeGC)
                let wordListAfterGC_Coordinates = List.mapi (fun i e ->((gtX, (gtY+i+1)), e)) wordListAfterGC
                printfn $"List before given coordinate {wordListBeforeGC_Coordinates} and after {wordListAfterGC_Coordinates}"
                
                let wl = wordListBeforeGC_Coordinates@wordListAfterGC_Coordinates
                
                let b = List.fold (fun acc e ->
                    match acc with
                    | Some v ->
                        printfn $"The tile before {e} is reserved by another tile."
                        acc
                    | None -> (isTileOccupied (fst e) st)) None wl
                match b with
                | None ->
                    printfn $"The word {wl} can be placed on board."
                    StateMonad.Success wl
                | _     -> StateMonad.Failure wl
            | false ->
                printfn $"failed"
                StateMonad.Failure [] //Not possible to plave the word
        
    let isPlaceable = true

    
    
    (*let selectFoundWord (st: State.state) (foundWords:word list)=
        debugPrint(sprintf " selectFoundWord with " + string (List.length foundWords))
        if (List.length foundWords = 0) then 
            List.empty, ((0,0)) //do something else?
        else 
            //check to only place word that does not touch other words
            let lst = List.filter (fun fw -> isPlaceable st fw) foundWords
            debugPrint(sprintf "Placeable words: " + (string (List.length lst)))
            if (List.length lst = 0) then List.empty, ((0,0))
            else 
                List.sortByDescending (fun (fw,(c,d)) -> List.length fw) lst
                |> List.head*)
    
    let changeTiles (st : State.state) = //if vildcard -> change tiles
        printfn $"Changing tiles"
        let hand = MultiSet.toList st.hand
        if st.bag > 2u
        then hand[0..2] 
        else hand[0..0]  
    
    let changeWildCard (st : State.state) =
        let hand = MultiSet.toList st.hand
        hand[0..0]
    
    let makeMove (st: State.state) (pieces : pieces) =
        if isBoardEmpty st
        then goThroughHand st (0, 0) pieces    
        else 
            
            let fw = [] //Map.fold (fun acc k v -> acc @ findWords st (fst (Map.find k st.placedTiles)) k (snd v)) List.empty placements |> State2.selectFoundWord st
            if (List.length fw = 0)
            then 
                debugPrint (sprintf " no found words - changing tiles ")
                List.empty
            else 
                []//makeMovePlayeble fw
        
        

module Scrabble =
    open System.Threading
    let playGame cstream pieces (st : State.state) =

        let rec aux (st : State.state) =
            Print.printHand pieces (State.hand st)
            let tilesToChange = Move.changeTiles st
            let move = Move.makeMove st pieces
            
            //if we can make words with the tiles available we play them, otherwise we change tiles
            if (move.Length = 0)
            then
                if st.boardTiles.Count > 91 
                then send cstream (SMPass)
                else send cstream (SMChange (tilesToChange))
            else
                send cstream (SMPlay [])
           
            debugPrint (sprintf "Player %d -> Server:\n%A\n" (State.playerNumber st) move)
            let msg = recv cstream
            
            //debugPrint (sprintf "Player %d <- Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.

            match msg with
            | RCM (CMPlaySuccess(ms, points, newPieces)) -> // vi kunne rykke nogle af tingene op i stedet for at vente til vi har fået besked fra serveren
                let movedTileOnBoard (m : (coord * (uint32 * (char * int))) list) : Map<coord, char> =
                    List.fold (fun acc e -> Map.add (fst e) (fst (snd (snd e))) acc ) Map.empty m
                
                let playedTiles = MultiSet.ofList (List.fold (fun acc ls -> (fst (snd ls))::acc) [] ms)
                let handWithoutPlayedTiles = MultiSet.subtract st.hand playedTiles
                
                let newHand = List.fold (fun acc (a, times) -> MultiSet.add a times acc) handWithoutPlayedTiles newPieces
                let newBag = st.bag - uint32(List.length newPieces)
                let newBT = Map.fold (fun acc k v -> Map.add k v acc ) st.boardTiles (movedTileOnBoard ms)
                
                let st' = State.mkState st.board st.dict st.playerNumber newHand newBag newBT   
                aux st'
                
            | RCM (CMChangeSuccess(newPieces)) ->
                let playedTiles = MultiSet.ofList (tilesToChange)
                let handWithoutPlayedTiles = MultiSet.subtract st.hand playedTiles 
                let newHand = List.fold (fun acc (a, times) -> MultiSet.add a times acc) handWithoutPlayedTiles newPieces
                
                let st' = State.mkState st.board st.dict st.playerNumber newHand st.bag  st.boardTiles 
                aux st'
                
            | RCM (CMPlayed (pid, ms, points)) -> // not relevant : since we do not offer multiplayer
                (* Successful play by other player. Update your state *)
                let st' = st // This state needs to be updated
                aux st'
               
            | RCM (CMPlayFailed (pid, ms)) -> // not relevant : since we do not offer multiplayer
                (* Failed play. Update your state *)
                let st' = st // This state needs to be updated
                aux st'

            | RCM (CMGameOver _) -> ()
            | RCM a -> failwith (sprintf "not implmented: %A" a)
            | RGPE err -> printfn "Gameplay Error:\n%A" err; aux st //gives error msg for all gpe and calls auc again for a new turn
        aux st

    let startGame 
            (boardP : boardProg) 
            (dictf : bool -> Dictionary.Dict) 
            (numPlayers : uint32) 
            (playerNumber : uint32) 
            (playerTurn  : uint32) 
            (hand : (uint32 * uint32) list)
            (tiles : Map<uint32, tile>)
            (timeout : uint32 option) 
            (cstream : Stream) =
        debugPrint 
            $"Starting game!
                      number of players = %d{numPlayers}
                      player id = %d{playerNumber}
                      player turn = %d{playerTurn}
                      hand =  %A{hand}
                      timeout = %A{timeout}\n\n"

        let dict = dictf false
        let board = Parser.mkBoard boardP
                  
        let handSet = List.fold (fun acc (x, k) -> MultiSet.add x k acc) MultiSet.empty hand

        fun () -> playGame cstream tiles (State.mkState board dict playerNumber handSet 91u Map.empty)
        