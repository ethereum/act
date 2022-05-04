{-# Language GADTs #-}
{-# Language DataKinds #-}

module Print where

import Prelude hiding (GT, LT)
import Data.ByteString.UTF8 (toString)

import Data.List

import Syntax
import Syntax.TimeAgnostic


prettyBehaviour :: Behaviour t -> String
prettyBehaviour (Behaviour name _ contract interface preconditions postconditions stateUpdates returns)
  =   "behaviour " <> name <> " of " <> contract
  >-< "interface " <> (show interface)
  <> prettyPre preconditions
  <> prettyStorage stateUpdates
  <> prettyRet returns
  <> prettyPost postconditions
  where
    prettyPre [] = ""
    prettyPre p = header "iff" >-< block (prettyExp <$> p)

    prettyStorage [] = ""
    prettyStorage s = header "storage" >-< block (prettyState <$> s)

    prettyState (Constant loc) = prettyLocation loc
    prettyState (Rewrite  rew) = prettyUpdate rew

    prettyRet (Just ret) = header "returns" >-< "  " <> prettyTypedExp ret
    prettyRet Nothing = ""

    prettyPost [] = ""
    prettyPost p = header "ensures" >-< block (prettyExp <$> p)

    header s = "\n\n" <> s <> "\n"
    block l = "  " <> intercalate "\n  " l
    x >-< y = x <> "\n" <> y

prettyExp :: Exp a t -> String
prettyExp e = case e of

  -- booleans
  Or _ a b -> print2 "or" a b
  Eq _ a b -> print2 "==" a b
  LT _ a b -> print2 "<" a b
  GT _ a b -> print2 ">" a b
  LEQ _ a b -> print2 "<=" a b
  GEQ _ a b -> print2 ">=" a b
  And _ a b -> print2 "and" a b
  NEq _ a b -> print2 "=/=" a b
  Neg _ a -> "(not " <> prettyExp a <> ")"
  Impl _ a b -> print2 "=>" a b
  LitBool _ b -> if b then "true" else "false"

  -- integers
  Add _ a b -> print2 "+" a b
  Sub _ a b -> print2 "-" a b
  Mul _ a b -> print2 "*" a b
  Div _ a b -> print2 "/" a b
  Mod _ a b -> print2 "%" a b
  Exp _ a b -> print2 "^" a b
  UIntMax _ a -> show $ uintmax a
  UIntMin _ a -> show $ uintmin a
  IntMax _ a -> show $ intmax a
  IntMin _ a -> show $ intmin a
  LitInt _ a -> show a
  IntEnv _ a -> prettyEnv a

  -- bytestrings
  Cat _ a b -> print2 "++" a b
  Slice _ a b c -> (prettyExp a) <> "[" <> (prettyExp b) <> ":" <> (prettyExp c) <> "]"
  ByStr _ a -> a
  ByLit _ a -> toString a
  ByEnv _ a -> prettyEnv a

  -- builtins
  NewAddr _ addr nonce -> "newAddr(" <> prettyExp addr <> ", " <> prettyExp nonce <> ")"

  --polymorphic
  ITE _ a b c -> "(if " <> prettyExp a <> " then " <> prettyExp b <> " else " <> prettyExp c <> ")"
  TEntry _ t a -> timeParens t $ prettyItem a
  Var _ _ x -> x
  where
    print2 sym a b = "(" <> prettyExp a <> " " <> sym <> " " <> prettyExp b <> ")"

prettyTypedExp :: TypedExp t -> String
prettyTypedExp (TExp _ e) = prettyExp e

prettyItem :: TStorageItem a t -> String
prettyItem item = contractFromItem item <> "." <> idFromItem item <> concatMap (brackets . prettyTypedExp) (ixsFromItem item)
  where
    brackets str = "[" <> str <> "]"

prettyLocation :: StorageLocation t -> String
prettyLocation (Loc _ item) = prettyItem item

prettyUpdate :: StorageUpdate t -> String
prettyUpdate (Update _ item e) = prettyItem item <> " => " <> prettyExp e

prettyEnv :: EthEnv -> String
prettyEnv e = case e of
  Caller -> "CALLER"
  Callvalue -> "CALLVALUE"
  Calldepth -> "CALLDEPTH"
  Origin -> "ORIGIN"
  Blockhash -> "BLOCKHASH"
  Blocknumber -> "BLOCKNUMBER"
  Difficulty -> "DIFFICULTY"
  Chainid -> "CHAINID"
  Gaslimit -> "GASLIMIT"
  Coinbase -> "COINBASE"
  Timestamp -> "TIMESTAMP"
  This -> "THIS"
  Nonce -> "NONCE"

-- | Invariant predicates are represented internally as a pair of timed
-- expressions, one over the prestate and one over the poststate.  This is good
-- since it keeps untimed expressions away from the various backends, and
-- maintains a nice seperation between the various compilation passes, but
-- unfortunately requires us to strip the timing out if we want to print the
-- invariant in a way that is easily digestible by humans, requiring a less
-- elegant implementation here than might be hoped for...
prettyInvPred :: InvariantPred Timed -> String
prettyInvPred = prettyExp . untime . fst
  where
    untimeTyped :: TypedExp t -> TypedExp Untimed
    untimeTyped (TExp t e) = TExp t (untime e)

    untime :: Exp a t -> Exp a Untimed
    untime e = case e of
      And p a b   -> And p (untime a) (untime b)
      Or p a b    -> Or p (untime a) (untime b)
      Impl p a b  -> Impl p (untime a) (untime b)
      Eq p a b    -> Eq p (untime a) (untime b)
      LT p a b    -> LT p (untime a) (untime b)
      LEQ p a b   -> LEQ p (untime a) (untime b)
      GT p a b    -> GT p (untime a) (untime b)
      GEQ p a b   -> GEQ p (untime a) (untime b)
      NEq p a b   -> NEq p (untime a) (untime b)
      Neg p a     -> Neg p (untime a)
      Add p a b   -> Add p (untime a) (untime b)
      Sub p a b   -> Sub p (untime a) (untime b)
      Mul p a b   -> Mul p (untime a) (untime b)
      Div p a b   -> Div p (untime a) (untime b)
      Mod p a b   -> Mod p (untime a) (untime b)
      Exp p a b   -> Exp p (untime a) (untime b)
      Cat p a b   -> Cat p (untime a) (untime b)
      ByStr p a   -> ByStr p a
      ByLit p a   -> ByLit p a
      LitInt p a  -> LitInt p a
      IntMin p a  -> IntMin p a
      IntMax p a  -> IntMax p a
      UIntMin p a -> UIntMin p a
      UIntMax p a -> UIntMax p a
      LitBool p a -> LitBool p a
      IntEnv p a  -> IntEnv p a
      ByEnv p a   -> ByEnv p a
      ITE p x y z -> ITE p (untime x) (untime y) (untime z)
      NewAddr p a b -> NewAddr p (untime a) (untime b)
      Slice p a b c -> Slice p (untime a) (untime b) (untime c)
      TEntry p _ (Item t a b c) -> TEntry p Neither (Item t a b (fmap untimeTyped c))
      Var p t a -> Var p t a
