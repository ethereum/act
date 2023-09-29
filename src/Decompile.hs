{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NoFieldSelectors #-}

{-|
Module      : Decompile
Description : Decompile EVM bytecode into Act

This module decompiles EVM bytecode into an Act spec. It operates as follows

1. Symbolically execute the bytecode to produce an EVM.Expr
2. Transform that Expr into one that can be safely represented using Integers
3. Convert that Expr into an Act spec (trusts solc compiler output)
4. Compile the generated Act spec back to Expr and check equivalence (solc compiler output no longer trusted)
-}
module Decompile where

import Debug.Trace

import Prelude hiding (LT, GT)

import Control.Monad.Except
import Control.Monad.Extra
import Data.Bifunctor
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromJust)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Typeable
import EVM.Fetch qualified as Fetch
import EVM.Solidity hiding (SlotType(..))
import EVM.Solidity qualified as EVM (SlotType(..))
import EVM.Types qualified as EVM
import EVM.Solvers (SolverGroup, withSolvers, Solver(..))
import EVM.SymExec
import EVM.Expr (simplify, isSuccess)
import GHC.IO

import Syntax.Annotated
import HEVM


data EVMContract = EVMContract
  { name :: Text
  , storageLayout :: Map Text StorageItem
  , runtime :: Map Interface (Set (EVM.Expr EVM.End))
  , creation :: (Interface, Set (EVM.Expr EVM.End))
  }
  deriving (Show, Eq)

-- | Explore both the initcode and runtimecode of the contract
explore :: SolverGroup -> SolcContract -> IO (Either Text EVMContract)
explore solvers contract = do
  ctor <- exploreCreation solvers contract
  behvs <- exploreRuntime solvers contract
  runExceptT $ do
    storage <- ExceptT . pure
      $ toErr "missing storage layout in compiler output" contract.storageLayout
    pure $ EVMContract
      { name = contract.contractName
      , storageLayout = storage
      , runtime = behvs
      , creation = ctor
      }

exploreRuntime :: SolverGroup -> SolcContract -> IO (Map Interface (Set (EVM.Expr EVM.End)))
exploreRuntime solvers contract = fmap (Map.fromList . Map.elems) $ forM contract.abiMap $ \method -> do
    let calldata = first (`writeSelector` method.methodSignature)
                 . (flip combineFragments) (EVM.AbstractBuf "txdata")
                 $ fmap (uncurry symAbiArg) method.inputs
    prestate <- stToIO $ abstractVM (fst calldata, []) contract.runtimeCode Nothing False
    expr <- simplify <$> interpret (Fetch.oracle solvers Nothing) Nothing 1 StackBased prestate runExpr
    let sucs = Set.fromList . filter isSuccess . flattenExpr $ expr
    let iface = behvIface method
    pure (iface, sucs)

exploreCreation :: SolverGroup -> SolcContract -> IO (Interface, Set (EVM.Expr EVM.End))
exploreCreation solvers contract = do
  -- TODO: doesn't this have a 4 byte gap at the front?
  let args = (flip combineFragments) (EVM.ConcreteBuf "") $ fmap (uncurry symAbiArg) contract.constructorInputs
  initVM <- stToIO $ abstractVM (fst args, []) contract.creationCode Nothing True
  expr <- simplify <$> interpret (Fetch.oracle solvers Nothing) Nothing 1 StackBased initVM runExpr
  let sucs = Set.fromList . filter isSuccess . flattenExpr $ expr
  pure (ctorIface contract.constructorInputs, sucs)

toErr :: Text -> Maybe a -> Either Text a
toErr _ (Just a) = Right a
toErr msg Nothing = Left msg

ctorIface :: [(Text, AbiType)] -> Interface
ctorIface args = Interface "constructor" (fmap (\(n, t) -> Decl t (T.unpack n)) args)

behvIface :: Method -> Interface
behvIface method = Interface (T.unpack method.name) (fmap (\(n, t) -> Decl t (T.unpack n)) method.inputs)

translate :: EVMContract -> Either Text Act
translate c = do
  contract <- liftM2 Contract (mkConstructor c) (mkBehvs c)
  let store = mkStore c
  pure $ Act store [contract]

mkStore :: EVMContract -> Store
mkStore c = Map.singleton (T.unpack c.name) (Map.mapKeys T.unpack $ fmap fromitem c.storageLayout)
  where
    fromitem item = (convslot item.slotType, toInteger item.slot)
    convslot (EVM.StorageMapping a b) = StorageMapping (fmap PrimitiveType a) (PrimitiveType b)
    convslot (EVM.StorageValue a) = StorageValue (PrimitiveType a)

mkConstructor :: EVMContract -> Either Text Constructor
mkConstructor cs
  | Set.size (snd cs.creation) == 1 =
      case head (Set.elems (snd cs.creation)) of
        EVM.Success props _ _ _ -> do
          ps <- mapM fromProp props
          pure $ Constructor
            { _cname = T.unpack cs.name
            , _cinterface = fst cs.creation
            , _cpreconditions = ps
            , _cpostconditions = mempty
            , _invariants = mempty
            , _initialStorage = mempty -- TODO
            , _cstateUpdates = mempty -- TODO
            }
        _ -> error "unexpected unsucessful branch"
  | otherwise = error "TODO: decompile constructors with multiple branches"

mkBehvs :: EVMContract -> Either Text [Behaviour]
mkBehvs c = concatMapM (\(i, bs) -> mapM (mkbehv i) (Set.toList bs)) (Map.toList c.runtime)
  where
    mkbehv :: Interface -> EVM.Expr EVM.End -> Either Text Behaviour
    mkbehv iface@(Interface method _) (EVM.Success props _ _ _) = do
      pres <- mapM fromProp props
      pure $ Behaviour
        { _contract = T.unpack c.name
        , _interface = iface
        , _name = method
        , _preconditions = pres
        , _caseconditions = mempty -- TODO: what to do here?
        , _postconditions = mempty
        , _stateUpdates = mempty -- TODO
        , _returns = Nothing -- TODO
        }
    mkbehv _ _ = error "unexpected unsucessful branch"

fromProp :: EVM.Prop -> Either Text (Exp ABoolean)
fromProp p = case p of
  EVM.PEq (a :: EVM.Expr t) b -> case eqT @t @EVM.EWord of
    Nothing -> Left $ "cannot decompile props comparing equality of non word terms: " <> T.pack (show p)
    Just Refl -> liftM2 (Eq nowhere SInteger) (fromWord a) (fromWord b)
  EVM.PLT a b -> liftM2 (LT nowhere) (fromWord a) (fromWord b)
  EVM.PGT a b -> liftM2 (LT nowhere) (fromWord a) (fromWord b)
  EVM.PGEq a b -> liftM2 (LT nowhere) (fromWord a) (fromWord b)
  EVM.PLEq a b -> liftM2 (LT nowhere) (fromWord a) (fromWord b)
  EVM.PNeg a -> fmap (Neg nowhere) (fromProp a)
  EVM.PAnd a b -> liftM2 (And nowhere) (fromProp a) (fromProp b)
  EVM.POr a b -> liftM2 (Or nowhere) (fromProp a) (fromProp b)
  EVM.PImpl a b -> liftM2 (Impl nowhere) (fromProp a) (fromProp b)
  EVM.PBool a -> pure $ LitBool nowhere a

fromWord :: EVM.Expr EVM.EWord -> Either Text (Exp AInteger)
fromWord w = case w of
  EVM.Lit a -> Right $ LitInt nowhere (toInteger a)
  -- TODO: get the actual abi type from the compiler output
  EVM.Var a -> Right $ Var nowhere SInteger (AbiBytesType 32) (T.unpack a)
  EVM.IsZero a -> do
    a' <- fromWord a
    Right $ ITE nowhere (Eq nowhere SInteger a' (LitInt nowhere 0)) (LitInt nowhere 1) (LitInt nowhere 0)
  EVM.TxValue -> Right $ IntEnv nowhere Callvalue
  _ -> Left $ "unable to decompile: " <> T.pack (show w)

verifyDecompilation :: ByteString -> ByteString -> Act -> IO ()
verifyDecompilation creation runtime spec =
  withSolvers CVC5 4 Nothing $ \solvers -> do
    let opts = defaultVeriOpts
    -- Constructor check
    checkConstructors solvers opts creation runtime spec
    -- Behavours check
    checkBehaviours solvers opts runtime spec
    -- ABI exhaustiveness sheck
    checkAbi solvers opts spec runtime


-- get full SolcContract from foundry project
test :: IO ()
test = do
  cs <- readBuildOutput "/home/me/src/mine/scratch/solidity" Foundry
  case cs of
    Left e -> print e
    Right (BuildOutput (Contracts o) _) -> do
      withSolvers CVC5 4 Nothing $ \solvers -> do
        let c = fromJust $ Map.lookup "src/basic.sol:Basic" o
        spec <- runExceptT $ do
          exprs <- ExceptT $ explore solvers c
          ExceptT (pure $ translate exprs)
        case spec of
          Left e -> print e
          Right s -> verifyDecompilation c.creationCode c.runtimeCode s

