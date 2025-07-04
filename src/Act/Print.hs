{-# Language GADTs #-}
{-# Language LambdaCase #-}
{-# Language DataKinds #-}

module Act.Print where

import Prelude hiding (GT, LT)
import Data.ByteString.UTF8 (toString)
import Prettyprinter hiding (brackets)
import qualified Prettyprinter.Render.Terminal as Term
import qualified Data.Text as Text

import System.IO (stdout)
import Data.Text qualified as T
import EVM.ABI (abiTypeSolidity)

import Data.List

import Act.Syntax.Typed
import Act.Syntax.Timing (timeParens)
import Act.Syntax.Types
import Act.Syntax.Untyped (ValueType(..), Pointer(..), EthEnv(..))

prettyAct :: Act -> String
prettyAct (Act _ contracts)
  = unlines (fmap prettyContract contracts)

prettyStore :: Store -> String
prettyStore = show

prettyContract :: Contract -> String
prettyContract (Contract ctor behvs) = unlines $ intersperse "\n" $ (prettyCtor ctor):(fmap prettyBehaviour behvs)

prettyCtor :: Constructor -> String
prettyCtor (Constructor name interface ptrs pres posts invs initStore)
  =   "constructor of " <> name
  >-< "interface " <> show interface
  <> prettyPtrs ptrs
  <> prettyPre pres
  <> prettyCreates initStore
  <> prettyPost posts
  <> prettyInvs invs
  where
    prettyCreates [] = ""
    prettyCreates s = header "creates" >-< block (prettyUpdate' <$> s)

    prettyInvs [] = ""
    prettyInvs _ = error "TODO: pretty print invariants"

    prettyUpdate' (Update _ (Item _ v r) e) = prettyValueType v <> " " <> prettyRef r <> " := " <> prettyExp e

prettyValueType :: ValueType -> String
prettyValueType = \case
  ContractType n -> n
  PrimitiveType t -> T.unpack (abiTypeSolidity t)


prettyBehaviour :: Behaviour -> String
prettyBehaviour (Behaviour name contract interface ptrs preconditions cases postconditions stateUpdates returns)
  =   "behaviour " <> name <> " of " <> contract
  >-< "interface " <> (show interface)
  <> prettyPtrs ptrs
  <> prettyPre preconditions
  <> prettyCases cases
  <> prettyStorage stateUpdates
  <> prettyRet returns
  <> prettyPost postconditions
  where
    prettyStorage [] = ""
    prettyStorage s = header "storage" >-< block (prettyUpdate <$> s)

    prettyRet (Just ret) = header "returns" >-< "  " <> prettyTypedExp ret
    prettyRet Nothing = ""



prettyPtrs :: [Pointer] -> String
prettyPtrs [] = ""
prettyPtrs ptrs = header "pointers" >-< block (prettyPtr <$> ptrs)
  where
    prettyPtr (PointsTo _ x c) = x <> " |-> " <> c

prettyPre :: [Exp ABoolean t] -> String
prettyPre [] = ""
prettyPre p = header "iff" >-< block (prettyExp <$> p)

prettyCases :: [Exp ABoolean t] -> String
prettyCases [] = ""
prettyCases [LitBool _ True] = ""
prettyCases p = header "case" >-< block (prettyExp <$> p) <> ":"

prettyPost :: [Exp ABoolean t] -> String
prettyPost [] = ""
prettyPost p = header "ensures" >-< block (prettyExp <$> p)

header :: String -> String
header s = "\n\n" <> s <> "\n"

block :: [String] -> String
block l = "  " <> intercalate "\n  " l

(>-<) :: String -> String -> String
x >-< y = x <> "\n" <> y

prettyExp :: Exp a t -> String
prettyExp e = case e of

  -- booleans
  Or _ a b -> print2 "or" a b
  Eq _ _ a b -> print2 "==" a b
  LT _ a b -> print2 "<" a b
  GT _ a b -> print2 ">" a b
  LEQ _ a b -> print2 "<=" a b
  GEQ _ a b -> print2 ">=" a b
  And _ a b -> print2 "and" a b
  NEq _ _ a b -> print2 "=/=" a b
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
  InRange _ a b -> "inRange(" <> show a <> ", " <> prettyExp b <> ")"
  LitInt _ a -> show a
  IntEnv _ a -> prettyEnv a

  -- bytestrings
  Cat _ a b -> print2 "++" a b
  Slice _ a b c -> (prettyExp a) <> "[" <> (prettyExp b) <> ":" <> (prettyExp c) <> "]"
  ByStr _ a -> a
  ByLit _ a -> toString a
  ByEnv _ a -> prettyEnv a

  -- contracts
  Create _ f ixs -> f <> "(" <> (intercalate "," $ fmap prettyTypedExp ixs) <> ")"

  --polymorphic
  ITE _ a b c -> "(if " <> prettyExp a <> " then " <> prettyExp b <> " else " <> prettyExp c <> ")"
  SVarRef _ t a -> timeParens t $ prettyItem a
  CVarRef _ a -> prettyItem a
  where
    print2 sym a b = "(" <> prettyExp a <> " " <> sym <> " " <> prettyExp b <> ")"

prettyTypedExp :: TypedExp t -> String
prettyTypedExp (TExp _ e) = prettyExp e

prettyItem :: TItem k a t -> String
prettyItem (Item _ _ r) = prettyRef r

prettyRef :: Ref k t -> String
prettyRef = \case
  CVar _ _ n -> n
  SVar _ _ n -> n
  SMapping _ r args -> prettyRef r <> concatMap (brackets . prettyTypedExp) args
  SField _ r _ n -> prettyRef r <> "." <> n
  where
    brackets str = "[" <> str <> "]"

prettyLocation :: StorageLocation -> String
prettyLocation (Loc _ t item) = timeParens t $ prettyItem item

prettyUpdate :: StorageUpdate -> String
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

-- | Doc type for terminal output
type DocAnsi = Doc Term.AnsiStyle

-- | prints a Doc, with wider output than the built in `putDoc`
render :: DocAnsi -> IO ()
render doc =
  let opts = LayoutOptions { layoutPageWidth = AvailablePerLine 120 0.9 } in
  Term.renderIO stdout (layoutPretty opts doc)

underline :: DocAnsi -> DocAnsi
underline = annotate Term.underlined

red :: DocAnsi -> DocAnsi
red = annotate (Term.color Term.Red)

yellow :: DocAnsi -> DocAnsi
yellow = annotate (Term.color Term.Yellow)

green :: DocAnsi -> DocAnsi
green = annotate (Term.color Term.Green)

bold :: DocAnsi -> DocAnsi
bold = annotate Term.bold

(<$$>) :: Doc ann -> Doc ann -> Doc ann
(<$$>) x y = vsep [x,y]

string :: String -> DocAnsi
string = pretty

text :: Text.Text -> DocAnsi
text = pretty

class PrettyAnsi a where
  prettyAnsi :: a -> DocAnsi
