{-
 -
 - coq backend for act
 -
 - unsupported features:
 - + bytestrings
 - + external storage
 - + specifications for multiple contracts
 -
 -}

{-# Language OverloadedStrings #-}
{-# LANGUAGE GADTs #-}

module Coq where

import qualified Data.Map.Strict    as M
import qualified Data.List.NonEmpty as NE
import qualified Data.Text          as T
import Data.Either (rights)
import Data.List (find, groupBy)
import Control.Monad.State

import EVM.ABI
import EVM.Solidity (SlotType(..))
import Syntax
import RefinedAst

type Store = M.Map Id SlotType
type Fresh = State Int

header :: T.Text
header =
  "(* --- GENERATED BY ACT --- *)\n\n\
  \Require Import Coq.ZArith.ZArith.\n\
  \Require Import ActLib.ActLib.\n\
  \Require Coq.Strings.String.\n\n\
  \Module " <> strMod <> " := Coq.Strings.String.\n\
  \Open Scope Z_scope.\n\n"

-- | produce a coq representation of a specification
coq :: Store -> [Claim] -> T.Text
coq store claims =

  header
  <> layout store <> "\n\n"
  <> block (evalSeq (claim store) <$> groups transitions)
  <> block (evalSeq retVal        <$> groups transitions)
  <> block (evalSeq (base store)  <$> groups constructors)
  <> reachable (groups constructors) (groups transitions)

  where

  behaviours = filter ((== Pass) . _mode) [a | B a <- claims]

  transitions = filter (not . _creation) behaviours

  constructors = filter _creation behaviours

  groups = groupBy (\b b' -> _name b == _name b')

  block xs = T.intercalate "\n\n" (concat xs) <> "\n\n"

  layout store' =
    "Record " <> stateType <> " : Set := " <> stateConstructor <> "\n{ "
    <> T.intercalate ("\n" <> "; ") (map decl pairs)
    <> "\n" <> "}." where
    pairs = M.toList store'
    decl (n, s) = (T.pack n) <> " : " <> slotType s


-- | inductive definition of reachable states
reachable :: [[Behaviour]] -> [[Behaviour]] -> T.Text
reachable constructors groups = inductive

  reachableType "" (stateType <> " -> " <> stateType <> " -> Prop") body

  where

  body = concat $
    (evalSeq baseCase <$> constructors)
    <>
    (evalSeq reachableStep <$> groups)

  reachableStep :: Behaviour -> Fresh T.Text
  reachableStep (Behaviour name _ _ _ i conds _ _ _) =
    fresh name >>= continuation where
    continuation name' =
      return $ name'
        <> stepSuffix <> " : forall "
        <> parens (baseVar <> " " <> stateVar <> " : " <> stateType)
        <> interface i <> ",\n"
        <> constructorBody where
      constructorBody = (indent 2) . implication . concat $
        [ [reachableType <> " " <> baseVar <> " " <> stateVar]
        , coqprop <$> conds
        , [ reachableType <> " " <> baseVar <> " "
            <> parens (name' <> " " <> stateVar <> " " <> arguments i)
          ]
        ]

  baseCase :: Behaviour -> Fresh T.Text
  baseCase (Behaviour name _ _ _ i@(Interface _ decls) conds _ _ _) =
    fresh name >>= continuation where
    continuation name' =
      return $ name'
        <> baseSuffix <> " : "
        <> universal <> "\n"
        <> constructorBody where
      baseval = parens $ name' <> " " <> arguments i
      constructorBody = (indent 2) . implication . concat $
        [ coqprop <$> conds
        , [reachableType <> " " <> baseval <> " " <> baseval]
        ]
      universal = if null decls
        then ""
        else "forall " <> interface i <> ","

-- | definition of a base state
base :: Store -> Behaviour -> Fresh T.Text
base store (Behaviour name _ _ _ i _ _ updates _) = do
  name' <- fresh name
  return $ definition name' (interface i) $
    stateval store (\_ t -> defaultValue t) (rights updates)

claim :: Store -> Behaviour -> Fresh T.Text
claim store (Behaviour name _ _ _ i _ _ updates _) = do
  name' <- fresh name
  return $ definition name' (stateDecl <> " " <> interface i) $
    stateval store (\n _ -> T.pack n <> " " <> stateVar) (rights updates)

-- | inductive definition of a return claim
-- ignores claims that do not specify a return value
retVal :: Behaviour -> Fresh T.Text
retVal (Behaviour name _ _ _ i conds _ _ (Just r)) =
  fresh name >>= continuation where
  continuation name' = return $ inductive
    (name' <> returnSuffix)
    (stateDecl <> " " <> interface i)
    (returnType r <> " -> Prop")
    [retname <> introSuffix <> " :\n" <> body] where

    retname = name' <> returnSuffix
    body = (indent 2) . implication . concat $
      [ coqprop <$> conds
      , [retname <> " " <> stateVar <> " " <> arguments i <> " " <> retexp r]
      ]

retVal _ = return ""

-- | produce a state value from a list of storage updates
-- 'handler' defines what to do in cases where a given name isn't updated
stateval
  :: Store
  -> (Id -> SlotType -> T.Text)
  -> [StorageUpdate]
  -> T.Text
stateval store handler updates =

  stateConstructor <> " " <> T.intercalate " "
    (map (valuefor updates) (M.toList store))

  where

  valuefor :: [StorageUpdate] -> (Id, SlotType) -> T.Text
  valuefor updates' (name, t) =
    case find (f name) updates' of
      Nothing -> parens $ handler name t
      Just (IntUpdate (DirectInt _ _) e) -> parens $ coqexp e
      Just (IntUpdate (MappedInt _ name' args) e) -> lambda (NE.toList args) 0 e name'
      Just (BoolUpdate (DirectBool _ _) e)  -> parens $ coqexp e
      Just (BoolUpdate (MappedBool _ name' args) e) -> lambda (NE.toList args) 0 e name'
      Just (BytesUpdate _ _) -> error "bytestrings not supported"

  -- filter by name
  f n (IntUpdate (DirectInt _ n') _)
    | n == n' = True
  f n (IntUpdate (MappedInt _ n' _) _)
    | n == n' = True
  f n (BoolUpdate (DirectBool _ n') _)
    | n == n' = True
  f n (BoolUpdate (MappedBool _ n' _) _)
    | n == n' = True
  f _ _ = False

  -- represent mapping update with anonymous function
  lambda :: [ReturnExp] -> Int -> Exp a -> Id -> T.Text
  lambda [] _ e _ = parens $ coqexp e
  lambda (x:xs) n e m = let name = anon <> T.pack (show n) in parens $ "fun "
    <> name
    <> " => if "
    <> name <> eqsym x <> retexp x <> " then " <> lambda xs (n + 1) e m <> " else "
    <> T.pack m <> " " <> stateVar <> " " <> lambdaArgs n

  lambdaArgs n = T.intercalate " " $ map (\x -> anon <> T.pack (show x)) [0..n]

  eqsym (ExpInt _) = " =? "
  eqsym (ExpBool _) = " =?? "
  eqsym (ExpBytes _) = error "bytestrings not supported"

-- | produce a block of declarations from an interface
interface :: Interface -> T.Text
interface (Interface _ decls) =
  T.intercalate " " (map decl decls) where
  decl (Decl t name) = parens $ T.pack name <> " : " <> abiType t

arguments :: Interface -> T.Text
arguments (Interface _ decls) =
  T.intercalate " " (map (\(Decl _ name) -> T.pack name) decls)

-- | coq syntax for a slot type
slotType :: SlotType -> T.Text
slotType (StorageMapping xs t) =
  T.intercalate " -> " (map abiType (NE.toList xs ++ [t]))
slotType (StorageValue abitype) = abiType abitype

-- | coq syntax for an abi type
abiType :: AbiType -> T.Text
abiType (AbiUIntType _) = "Z"
abiType (AbiIntType _) = "Z"
abiType AbiAddressType = "address"
abiType AbiStringType = strMod <> ".string"
abiType a = error $ show a

-- | coq syntax for a return type
returnType :: ReturnExp -> T.Text
returnType (ExpInt _) = "Z"
returnType (ExpBool _) = "bool"
returnType (ExpBytes _) = "bytestrings not supported"

-- | default value for a given type
-- this is used in cases where a value is not set in the constructor
defaultValue :: SlotType -> T.Text
defaultValue t =

  case t of
    (StorageMapping xs t') -> "fun "
      <> T.intercalate " " (replicate (length (NE.toList xs)) "_")
      <> " => "
      <> abiVal t'
    (StorageValue t') -> abiVal t'

  where

  abiVal (AbiUIntType _) = "0"
  abiVal (AbiIntType _) = "0"
  abiVal AbiAddressType = "0"
  abiVal AbiStringType = strMod <> ".EmptyString"
  abiVal _ = error "TODO: missing default values"

-- | coq syntax for an expression
coqexp :: Exp a -> T.Text

-- booleans
coqexp (LitBool True)  = "true"
coqexp (LitBool False) = "false"
coqexp (BoolVar name) = T.pack name
coqexp (And e1 e2)  = parens $ "andb "   <> coqexp e1 <> " " <> coqexp e2
coqexp (Or e1 e2)   = parens $ "orb"     <> coqexp e1 <> " " <> coqexp e2
coqexp (Impl e1 e2) = parens $ "implb"   <> coqexp e1 <> " " <> coqexp e2
coqexp (Eq e1 e2)   = parens $ coqexp e1  <> " =? " <> coqexp e2
coqexp (NEq e1 e2)  = parens $ "negb " <> parens (coqexp e1  <> " =? " <> coqexp e2)
coqexp (Neg e)      = parens $ "negb " <> coqexp e
coqexp (LE e1 e2)   = parens $ coqexp e1 <> " <? "  <> coqexp e2
coqexp (LEQ e1 e2)  = parens $ coqexp e1 <> " <=? " <> coqexp e2
coqexp (GE e1 e2)   = parens $ coqexp e2 <> " <? "  <> coqexp e1
coqexp (GEQ e1 e2)  = parens $ coqexp e2 <> " <=? " <> coqexp e1
coqexp (TEntry (DirectBool _ name)) = parens $ T.pack name <> " " <> stateVar
coqexp (TEntry (MappedBool _ name args)) = parens $
  T.pack name <> " s " <> coqargs args

-- integers
coqexp (LitInt i) = T.pack $ show i
coqexp (IntVar name) = T.pack name
coqexp (Add e1 e2) = parens $ coqexp e1 <> " + " <> coqexp e2
coqexp (Sub e1 e2) = parens $ coqexp e1 <> " - " <> coqexp e2
coqexp (Mul e1 e2) = parens $ coqexp e1 <> " * " <> coqexp e2
coqexp (Div e1 e2) = parens $ coqexp e1 <> " / " <> coqexp e2
coqexp (Mod e1 e2) = parens $ "Z.modulo " <> coqexp e1 <> coqexp e2
coqexp (Exp e1 e2) = parens $ coqexp e1 <> " ^ " <> coqexp e2
coqexp (IntMin n)  = parens $ "INT_MIN "  <> T.pack (show n)
coqexp (IntMax n)  = parens $ "INT_MAX "  <> T.pack (show n)
coqexp (UIntMin n) = parens $ "UINT_MIN " <> T.pack (show n)
coqexp (UIntMax n) = parens $ "UINT_MAX " <> T.pack (show n)
coqexp (TEntry (DirectInt _ name)) = parens $ T.pack name <> " " <> stateVar
coqexp (TEntry (MappedInt _ name args)) = parens $
  T.pack name <> " s " <> coqargs args

-- polymorphic
coqexp (ITE b e1 e2) = parens $ "if "
  <> coqexp b
  <> " then "
  <> coqexp e1
  <> " else "
  <> coqexp e2

-- unsupported
coqexp (IntEnv e) = error $ show e <> ": environment values not yet supported"
coqexp (Cat _ _) = error "bytestrings not supported"
coqexp (Slice _ _ _) = error "bytestrings not supported"
coqexp (ByVar _) = error "bytestrings not supported"
coqexp (ByStr _) = error "bytestrings not supported"
coqexp (ByLit _) = error "bytestrings not supported"
coqexp (ByEnv _) = error "bytestrings not supported"
coqexp (TEntry (DirectBytes _ _)) = error "bytestrings not supported"
coqexp (TEntry (MappedBytes _ _ _)) = error "bytestrings not supported"
coqexp (NewAddr _ _) = error "newaddr not supported"

-- | coq syntax for a proposition
coqprop :: Exp a -> T.Text
coqprop (LitBool True)  = "True"
coqprop (LitBool False) = "False"
coqprop (And e1 e2)  = parens $ coqprop e1 <> " /\\ " <> coqprop e2
coqprop (Or e1 e2)   = parens $ coqprop e1 <> " \\/ " <> coqprop e2
coqprop (Impl e1 e2) = parens $ coqprop e1 <> " -> " <> coqprop e2
coqprop (Neg e)      = parens $ "not " <> coqprop e
coqprop (Eq e1 e2)   = parens $ coqexp e1 <> " = "  <> coqexp e2
coqprop (NEq e1 e2)  = parens $ coqexp e1 <> " <> " <> coqexp e2
coqprop (LE e1 e2)   = parens $ coqexp e1 <> " < "  <> coqexp e2
coqprop (LEQ e1 e2)  = parens $ coqexp e1 <> " <= " <> coqexp e2
coqprop (GE e1 e2)   = parens $ coqexp e2 <> " > "  <> coqexp e1
coqprop (GEQ e1 e2)  = parens $ coqexp e2 <> " >= " <> coqexp e1
coqprop _ = error "ill formed proposition"

-- | coq syntax for a return expression
retexp :: ReturnExp -> T.Text
retexp (ExpInt e)   = coqexp e
retexp (ExpBool e)  = coqexp e
retexp (ExpBytes _) = error "bytestrings not supported"

-- | coq syntax for a list of arguments
coqargs :: NE.NonEmpty ReturnExp -> T.Text
coqargs (e NE.:| es) =
  retexp e <> " " <> T.intercalate " " (map retexp es)

fresh :: Id -> Fresh T.Text
fresh name = state $ \s -> (T.pack (name <> show s), s + 1)

evalSeq :: Traversable t => (a -> Fresh b) -> t a -> t b
evalSeq f xs = evalState (sequence (f <$> xs)) 0

--- text manipulation ---

definition :: T.Text -> T.Text -> T.Text -> T.Text
definition name args value =
  "Definition " <> name <> " " <> args <> " :=\n" <> value <> "\n."

inductive :: T.Text -> T.Text -> T.Text -> [T.Text] -> T.Text
inductive name args indices constructors =
  "Inductive " <> name <> " " <> args <> " : " <> indices <> " :=\n"
  <> T.intercalate "\n" (("| " <>) <$> constructors) <> "\n."

-- | multiline implication
implication :: [T.Text] -> T.Text
implication xs = "   " <> T.intercalate "\n-> " xs

-- | wrap text in parentheses
parens :: T.Text -> T.Text
parens s = "(" <> s <> ")"

indent :: Int -> T.Text -> T.Text
indent n text = T.unlines $ ((T.replicate n " ") <>) <$> (T.lines text)


--- constants ---

-- | string module name
strMod :: T.Text
strMod  = "Str"

-- | base state name
baseVar :: T.Text
baseVar = "BASE"

stateType :: T.Text
stateType = "State"

stateVar :: T.Text
stateVar = "STATE"

stateDecl :: T.Text
stateDecl = parens $ stateVar <> " : " <> stateType

stateConstructor :: T.Text
stateConstructor = "state"

returnSuffix :: T.Text
returnSuffix = "_ret"

baseSuffix :: T.Text
baseSuffix = "_base"

stepSuffix :: T.Text
stepSuffix = "_step"

introSuffix :: T.Text
introSuffix = "_intro"

reachableType :: T.Text
reachableType = "reachable"

anon :: T.Text
anon = "_binding_"
