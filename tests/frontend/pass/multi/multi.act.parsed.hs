[Definition "a" constructor() [] (Creates [AssignVal (StorageVar uint256 "x") (IntLit (AlexPn 63 5 14) 0)]) [] [] [],Definition "B" constructor() [] (Creates [AssignVal (StorageVar uint256 "y") (IntLit (AlexPn 129 11 14) 0)]) [] [] [],Transition "remote" "B" set_remote(uint256 z) [Iff (AlexPn 185 17 1) [EEq (AlexPn 202 18 14) (EnvExp (AlexPn 192 18 4) Callvalue) (IntLit (AlexPn 205 18 17) 0)]] (Direct (Post Nothing [ExtStorage "a" [Rewrite (Entry (AlexPn 370 24 4) "x" []) (EntryExp (AlexPn 375 24 9) "z" [])]] Nothing)) [],Transition "multi" "B" set_remote(uint256 z) [Iff (AlexPn 429 29 1) [EEq (AlexPn 446 30 14) (EnvExp (AlexPn 436 30 4) Callvalue) (IntLit (AlexPn 449 30 17) 0)]] (Direct (Post (Just [Rewrite (Entry (AlexPn 517 34 4) "y" []) (IntLit (AlexPn 522 34 9) 1)]) [ExtStorage "a" [Rewrite (Entry (AlexPn 538 37 4) "x" []) (EntryExp (AlexPn 543 37 9) "z" [])]] Nothing)) []]
