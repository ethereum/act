[Constructor "init" "Token" (Interface "constructor"
                             [])
  []
(CDirect (PostCreates [AssignMany (StorageDec (Mapping T_address (Direct (T_uint 256))) "balanceOf") []] [])
) Nothing,
Transition "mint" "Token" (Interface "mint"
                           [Dec (T_uint 256) "value"])
  []
(TDirect (Post (Just [(Entry (P 0 0 0) "balanceOf" [EnvExpr (P 0 0 0) CALLER],
                EAdd (P 0 0 0)
                (EntryExp (Entry (P 0 0 0) "balanceOf" [EnvExpr (P 0 0 0) CALLER]))
                (Var (P 0 0 0) "value"))])
           []
           Nothing)

) Nothing
 ]
