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
        boardTiles    : Map<coord, char>
    }

    let mkState b d pn h bt = {board = b; dict = d;  playerNumber = pn; hand = h; boardTiles = bt }

    let board st         = st.board
    let dict st          = st.dict
    let playerNumber st  = st.playerNumber
    let hand st          = st.hand
    let boardTile st = st.boardTiles

        
module Move =
    
    type coord = (int * int)
    type letter = uint32 * char
    type word = List<coord * letter>
    type pieces = Map<uint32,Set<char*int>>
    
    let isBoardEmpty (st: State.state) = Map.count st.boardTiles = 0

    let findWords (st: State.state) (id: uint32) (co: coord) (pieces : pieces) =
        let mutable updatedDict = st.dict
        let rec aux
            (dict: Dictionary.Dict)
            (hand: MultiSet.MultiSet<uint32>)
            (ids: List<uint32 * char>)
            (foundWords: List<List<uint32 * char> * coord>)
            =
            MultiSet.fold
                (fun fw id v ->
                    Set.fold (fun _ (c,_) -> 
                        match Dictionary.step c dict with
                        | None -> fw
                        | Some (true, dict) ->
                            updatedDict <- dict
                            aux dict (MultiSet.removeSingle id hand) (ids @ [ (id, c) ]) (((ids @ [ (id, c) ]),(co)) :: fw) 
                        | Some (false, dict) ->
                            updatedDict <- dict
                            aux dict (MultiSet.removeSingle id hand) (ids @ [ (id, c) ]) fw
                    ) foundWords (Map.find id pieces) 
                )
                foundWords
                hand

        aux updatedDict (st.hand) list.Empty list.Empty 
   
    let isTileOccupied (c: coord) (st: State.state) =
        match st.boardTiles.TryFind c with
        | Some v    -> Some v
        | None      -> None
        
    let findCoordsForWord (w : letter list) (gcCoords : coord) (givenTile : letter) (st : State.state) : StateMonad.Result<'a, word>  = 
        let gtX, gtY = gcCoords
        let givenTileChar = (snd givenTile)
        let positionInWord = List.findIndex (fun x -> givenTileChar = (snd x) ) w
        
        let wordListBeforeGC    = w[0..positionInWord-1]
        let wordListAfterGC     = w[positionInWord+1..]
        
        let left = (isTileOccupied (gtX-1, gtY) st).IsNone
        let right = (isTileOccupied (gtX+1, gtY) st).IsNone
        
        let up = (isTileOccupied (gtX, gtY-1) st).IsNone
        let down = (isTileOccupied (gtX, gtY+1) st).IsNone
        
        let horizontal = (left&&right)
        let vertical = (up&&down)
        
        match (horizontal) with
        | true ->
            printfn $"Trying horizontal:"
            let wordListBeforeGC_Coordinates = List.mapi (fun i e ->(((gtX-i-1), gtY), e)) (wordListBeforeGC)
            let wordListAfterGC_Coordinates = List.mapi (fun i e ->(((gtX+i+1), gtY), e)) wordListAfterGC
            printfn $"List before given coordinate {wordListBeforeGC_Coordinates} and after {wordListAfterGC_Coordinates}"

            let (word:word) = wordListBeforeGC_Coordinates@wordListAfterGC_Coordinates
            
            let isAnyTilesDisturbing = List.fold (fun acc e ->
                match acc with
                | Some v ->
                    printfn $"The tile before {e} is reserved by another tile."
                    acc
                | None -> (isTileOccupied (fst e) st)) None word //up down 
            
            match isAnyTilesDisturbing with
            | None ->
                printfn $"The word {word} can be placed on board."
                StateMonad.Success word
            | _     -> StateMonad.Failure word
            
        | false ->
            match (vertical) with
            |true -> 
                printfn $"Trying vertical:"
                let wordListBeforeGC_Coordinates = List.mapi (fun i e ->((gtX, (gtY-i-1)), e)) (List.rev wordListBeforeGC)
                let wordListAfterGC_Coordinates = List.mapi (fun i e ->((gtX, (gtY+i+1)), e)) wordListAfterGC
                printfn $"List before given coordinate {wordListBeforeGC_Coordinates} and after {wordListAfterGC_Coordinates}"
                
                let wl = wordListBeforeGC_Coordinates@wordListAfterGC_Coordinates
                
                let isAnyTilesDisturbing = List.fold (fun acc e ->
                    match acc with
                    | Some v ->
                        printfn $"The tile before {e} is reserved by another tile."
                        acc
                    | None -> (isTileOccupied (fst e) st)) None wl //left right 
                match isAnyTilesDisturbing with
                | None ->
                    printfn $"The word {wl} can be placed on board."
                    StateMonad.Success wl
                | _     -> StateMonad.Failure wl
            | false ->
                printfn $"failed"
                StateMonad.Failure [] //Not possible to plave the word
    
        
    
    let selectFoundWord (st: State.state) (foundWords:word list)=
       ()// List.fold (fun w ->  ) [] foundWords
    
    let changeTiles (st : State.state) = //if vildcard -> change tiles
        printfn $"Changing tiles"
        let hand = MultiSet.toList st.hand
        if st.boardTiles.Count < 90
        then hand[0..2] 
        else hand[0..0]  
   
    
    let firstMove (id:uint32) (co:coord) (pieces:pieces) (st:State.state) =
        let rec aux di hand word (foundWords: ((uint32 * char) list) list) =
            MultiSet.fold
                  (fun acc id _ ->
                        Set.fold( fun _ (c,_) ->
                            match Dictionary.step c di  with
                            | None -> acc
                            | Some(true,di) ->
                               
                                aux di (MultiSet.removeSingle id hand) (word @ [(id,c)]) ((word @ [(id,c)]) :: foundWords)
                            | Some(false,di) ->
                                
                                aux di (MultiSet.removeSingle id hand) (word @ [(id,c)]) foundWords
                        ) foundWords (Map.find id pieces)
                        
                    
                )foundWords hand
        
        let di =
            if (st.boardTiles.Count = 0)
            then
                match (Dictionary.step (fst (Set.minElement (Map.find id pieces))) st.dict) with
                | None -> st.dict //Do we ever get here?
                | Some (_, d) -> d
            else
                match (Dictionary.step (Map.find co st.boardTiles) st.dict) with
                | None -> st.dict //Do we ever get here?
                | Some (_, d) -> d
        
        aux di st.hand [] []
        
    let otherMove : (coord * (uint32 * (char * int))) list = []
    
    let goThroughHand (st : State.state) (c: coord) (pieces : pieces) =
        MultiSet.fold (fun acc id _ -> acc @ (findWords st id c pieces)) List.Empty st.hand
    
    
    //find the best word to play on the bord. if no words found then return a empty list, such that we know when to exchange
    let makeMove (st: State.state) (pieces : pieces) =
        let l = goThroughHand(st)
        match isBoardEmpty st with
        | true ->
            //(l (0,0) pieces)[0] |> List.iter (fun x -> printf "%d " x)
            printfn $"Heh? {(l (0,0) pieces)[0]}"
            []
        | false -> [] //otherMove
        
        

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
                let newBT = Map.fold (fun acc k v -> Map.add k v acc ) st.boardTiles (movedTileOnBoard ms)
                
                let st' = State.mkState st.board st.dict st.playerNumber newHand newBT   
                aux st'
                
            | RCM (CMChangeSuccess(newPieces)) ->
                let playedTiles = MultiSet.ofList (tilesToChange)
                let handWithoutPlayedTiles = MultiSet.subtract st.hand playedTiles 
                let newHand = List.fold (fun acc (a, times) -> MultiSet.add a times acc) handWithoutPlayedTiles newPieces
                
                let st' = State.mkState st.board st.dict st.playerNumber newHand st.boardTiles 
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

        fun () -> playGame cstream tiles (State.mkState board dict playerNumber handSet Map.empty)
        