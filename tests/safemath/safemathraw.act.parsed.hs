[Transition "add" "SafeAdd" add(uint256 y, uint256 x) [Iff (AlexPn 95 8 1) [EEq (AlexPn 114 10 15) (EnvExp (AlexPn 104 10 5) Callvalue) (IntLit 0)],IffIn (AlexPn 62 4 1) uint256 [EAdd (AlexPn 90 6 7) (EntryExp (AlexPn 88 6 5) "x" []) (EntryExp (AlexPn 92 6 9) "y" [])]] (Direct (Post Nothing [] (Just (EAdd (AlexPn 130 12 11) (EntryExp (AlexPn 128 12 9) "x" []) (EntryExp (AlexPn 132 12 13) "y" []))))) Nothing]
