{-# Language GADTs #-}
{-# Language DataKinds #-}

module Print where

import Data.ByteString.UTF8 (toString)

import Data.List

import Syntax
import Syntax.TimeAgnostic

import qualified Syntax.Annotated as Annotated
import qualified Syntax.TimeAgnostic as Agnostic

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
  Or a b -> print2 "or" a b
  Eq a b -> print2 "==" a b
  LE a b -> print2 "<" a b
  GE a b -> print2 ">" a b
  LEQ a b -> print2 "<=" a b
  GEQ a b -> print2 ">=" a b
  And a b -> print2 "and" a b
  NEq a b -> print2 "=/=" a b
  Neg a -> "(not " <> prettyExp a <> ")"
  Impl a b -> print2 "=>" a b
  LitBool b -> if b then "true" else "false"
  BoolVar b -> b

  -- integers
  Add a b -> print2 "+" a b
  Sub a b -> print2 "-" a b
  Mul a b -> print2 "*" a b
  Div a b -> print2 "/" a b
  Mod a b -> print2 "%" a b
  Exp a b -> print2 "^" a b
  UIntMax a -> show $ uintmax a
  UIntMin a -> show $ uintmin a
  IntMax a -> show $ intmax a
  IntMin a -> show $ intmin a
  LitInt a -> show a
  IntVar a -> a
  IntEnv a -> prettyEnv a

  -- bytestrings
  Cat a b -> print2 "++" a b
  Slice a b c -> (prettyExp a) <> "[" <> (prettyExp b) <> ":" <> (prettyExp c) <> "]"
  ByVar a -> a
  ByStr a -> a
  ByLit a -> toString a
  ByEnv a -> prettyEnv a

  -- builtins
  NewAddr addr nonce -> "newAddr(" <> prettyExp addr <> ", " <> prettyExp nonce <> ")"

  --polymorphic
  ITE a b c -> "(if " <> prettyExp a <> " then " <> prettyExp b <> " else " <> prettyExp c <> ")"
  TEntry a t -> timeParens t $ prettyItem a
  where
    print2 sym a b = "(" <> prettyExp a <> " " <> sym <> " " <> prettyExp b <> ")"

prettyTypedExp :: TypedExp t -> String
prettyTypedExp e = case e of
  ExpInt e' -> prettyExp e'
  ExpBool e' -> prettyExp e'
  ExpBytes e' -> prettyExp e'

prettyItem :: TStorageItem a t -> String
prettyItem item = contractFromItem item <> "." <> idFromItem item <> concatMap (brackets . prettyTypedExp) (ixsFromItem item)
  where
    brackets str = "[" <> str <> "]"

prettyLocation :: StorageLocation t -> String
prettyLocation (IntLoc item) = prettyItem item
prettyLocation (BoolLoc item) = prettyItem item
prettyLocation (BytesLoc item) = prettyItem item

prettyUpdate :: StorageUpdate t -> String
prettyUpdate (IntUpdate item e) = prettyItem item <> " => " <> prettyExp e
prettyUpdate (BoolUpdate item e) = prettyItem item <> " => " <> prettyExp e
prettyUpdate (BytesUpdate item e) = prettyItem item <> " => " <> prettyExp e

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
prettyInvPred = prettyExp . stripTime . fst
  where
    stripTimeTyped :: Annotated.TypedExp -> Agnostic.TypedExp Untimed
    stripTimeTyped (ExpInt e) = ExpInt (stripTime e)
    stripTimeTyped (ExpBool e) = ExpBool (stripTime e)
    stripTimeTyped (ExpBytes e) = ExpBytes (stripTime e)

    -- | Strip timing from an annotated expression, sometimes useful for display in the ui
    stripTime :: Annotated.Exp a -> Agnostic.Exp a Untimed
    stripTime e = case e of
      And a b   -> And (stripTime a) (stripTime b)
      Or a b    -> Or (stripTime a) (stripTime b)
      Impl a b  -> Impl (stripTime a) (stripTime b)
      Eq a b    -> Eq (stripTime a) (stripTime b)
      LE a b    -> LE (stripTime a) (stripTime b)
      LEQ a b   -> LEQ (stripTime a) (stripTime b)
      GE a b    -> GE (stripTime a) (stripTime b)
      GEQ a b   -> GEQ (stripTime a) (stripTime b)
      NEq a b   -> NEq (stripTime a) (stripTime b)
      Neg a     -> Neg (stripTime a)
      Add a b   -> Add (stripTime a) (stripTime b)
      Sub a b   -> Sub (stripTime a) (stripTime b)
      Mul a b   -> Mul (stripTime a) (stripTime b)
      Div a b   -> Div (stripTime a) (stripTime b)
      Mod a b   -> Mod (stripTime a) (stripTime b)
      Exp a b   -> Exp (stripTime a) (stripTime b)
      Cat a b   -> Cat (stripTime a) (stripTime b)
      ByVar a   -> ByVar a
      ByStr a   -> ByStr a
      ByLit a   -> ByLit a
      LitInt a  -> LitInt a
      IntMin a  -> IntMin a
      IntMax a  -> IntMax a
      UIntMin a -> UIntMin a
      UIntMax a -> UIntMax a
      IntVar a  -> IntVar a
      LitBool a -> LitBool a
      BoolVar a -> BoolVar a
      IntEnv a  -> IntEnv a
      ByEnv a   -> ByEnv a
      ITE x y z -> ITE (stripTime x) (stripTime y) (stripTime z)
      NewAddr a b -> NewAddr (stripTime a) (stripTime b)
      Slice a b c -> Slice (stripTime a) (stripTime b) (stripTime c)
      TEntry (IntItem a b c) _ -> TEntry (IntItem a b (fmap stripTimeTyped c)) Neither
      TEntry (BoolItem a b c) _ -> TEntry (BoolItem a b (fmap stripTimeTyped c)) Neither
      TEntry (BytesItem a b c) _ -> TEntry (BytesItem a b (fmap stripTimeTyped c)) Neither

