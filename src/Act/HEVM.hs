{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

{-# LANGUAGE DuplicateRecordFields #-}

module Act.HEVM where

import Prelude hiding (GT, LT)

import qualified Data.Map as M
import Data.List
import Data.Containers.ListUtils (nubOrd)
import qualified Data.Text as T
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8 (pack)
import Data.ByteString (ByteString)
import Data.Text.Encoding (encodeUtf8)
import Control.Concurrent.Async
import Control.Monad
import Data.DoubleWord
import Data.Maybe
import Data.Type.Equality (TestEquality(..), (:~:)(..))
import Control.Monad.State
import Data.List.NonEmpty qualified as NE
import Data.Validation
import Data.Text.Lazy.Builder

import Act.HEVM_utils
import Act.Syntax.Annotated as Act
import Act.Syntax.Untyped (makeIface)
import Act.Syntax
import Act.Error
import Act.Print

import qualified Act.SMT as SMT

import EVM.ABI (Sig(..))
import EVM as EVM hiding (bytecode)
import qualified EVM.Types as EVM hiding (FrameState(..))
import EVM.Expr hiding (op2, inRange)
import EVM.SymExec hiding (EquivResult, isPartial)
import qualified EVM.SymExec as SymExec (EquivResult)
import EVM.SMT (SMTCex(..), assertProps, SMT2(..))
import EVM.Solvers
import EVM.Effects
import EVM.Format as Format
import EVM.Traversals

import Debug.Trace

type family ExprType a where
  ExprType 'AInteger  = EVM.EWord
  ExprType 'ABoolean  = EVM.EWord
  ExprType 'AByteStr  = EVM.Buf
  ExprType 'AContract = EVM.EWord -- address?

type Layout = M.Map Id (M.Map Id Integer)

type ContractMap = M.Map (EVM.Expr EVM.EAddr) (EVM.Expr EVM.EContract)

-- | For each contract in the Act spec, put in a codemap its Act
-- specification, init code, and runtimecode. This is being looked up
-- when we encounter a constructor call.
type CodeMap = M.Map Id (Contract, BS.ByteString, BS.ByteString)

type EquivResult = ProofResult () (T.Text, SMTCex) ()

initAddr :: EVM.Expr EVM.EAddr
initAddr = EVM.SymAddr "entrypoint"

slotMap :: Store -> Layout
slotMap store =
  M.map (M.map (\(_, slot) -> slot)) store


-- * Act state monad

data ActEnv = ActEnv
  { codemap :: CodeMap
  , fresh   :: Int
  , layout  :: Layout
  , caddr   :: EVM.Expr EVM.EAddr
  , caller  :: Maybe (EVM.Expr EVM.EAddr)
  }

type ActM a = State ActEnv a

getCodemap :: ActM CodeMap
getCodemap = do
  env <- get
  pure env.codemap

getFreshIncr :: ActM Int
getFreshIncr = do
  env <- get
  let fresh = env.fresh
  put (env { fresh = fresh + 1 })
  pure (fresh + 1)

getFresh :: ActM Int
getFresh = do
  env <- get
  pure env.fresh

getLayout :: ActM Layout
getLayout = do
  env <- get
  pure env.layout

getCaddr :: ActM (EVM.Expr EVM.EAddr)
getCaddr = do
  env <- get
  pure env.caddr

localCaddr :: EVM.Expr EVM.EAddr -> ActM a -> ActM a
localCaddr caddr m = do
  env <- get
  let caddr' = env.caddr
  let caller' = env.caller
  put (env { caddr = caddr, caller = Just caddr' })
  res <- m
  env' <- get
  put (env' { caddr = caddr', caller =  caller' })
  pure res

getCaller :: ActM (EVM.Expr EVM.EAddr)
getCaller = do
  env <- get
  case env.caller of
    Just c -> pure c
    Nothing -> pure $ EVM.SymAddr "caller" -- Zoe: not sure what to put here


-- * Act translation

translateConstructor ::  BS.ByteString -> Constructor -> ContractMap -> ActM ([EVM.Expr EVM.End], Calldata, Sig)
translateConstructor bytecode (Constructor _ iface preconds _ _ upds) cmap = do
  fresh <- getFresh
  let initmap =  M.insert initAddr initcontract cmap
  preconds' <- mapM (toProp initmap) preconds
  cmap' <- applyUpdates initmap initmap upds
  fresh' <- getFresh
  pure $ ([EVM.Success (snd calldata <> preconds' <> symAddrCnstr (fresh+1) fresh') mempty (EVM.ConcreteBuf bytecode) cmap'], calldata, ifaceToSig iface)
  where
    calldata = makeCtrCalldata iface
    initcontract = EVM.C { EVM.code    = EVM.RuntimeCode (EVM.ConcreteRuntimeCode bytecode)
                         , EVM.storage = EVM.ConcreteStore mempty
                         , EVM.balance = EVM.Lit 0
                         , EVM.nonce   = Just 1
                         }


symAddrCnstr :: Int -> Int -> [EVM.Prop]
symAddrCnstr start end = fmap (\i -> EVM.PNeg (EVM.PEq (EVM.WAddr (EVM.SymAddr $ "freshSymAddr" <> (T.pack $ show i))) (EVM.Lit 0))) [start..end]

translateBehvs :: ContractMap -> [Behaviour] ->  ActM [(Id, [EVM.Expr EVM.End], Calldata, Sig)]
translateBehvs cmap behvs = do
  let groups = (groupBy sameIface behvs) :: [[Behaviour]]
  mapM (\behvs' -> do
           exprs <- mapM (translateBehv cmap) behvs'
           pure (behvName behvs', exprs, behvCalldata behvs', behvSig behvs)) groups
  where
    behvCalldata (Behaviour _ _ iface _ _ _ _ _:_) = makeCalldata iface
    behvCalldata [] = error "Internal error: behaviour groups cannot be empty"

    behvSig (Behaviour _ _ iface _ _ _ _ _:_) = ifaceToSig iface
    behvSig [] = error "Internal error: behaviour groups cannot be empty"

    -- TODO remove reduntant name in behaviours
    sameIface (Behaviour _ _ iface  _ _ _ _ _) (Behaviour _ _ iface' _ _ _ _ _) =
      makeIface iface == makeIface iface'

    behvName (Behaviour _ _ (Interface name _) _ _ _ _ _:_) = name
    behvName [] = error "Internal error: behaviour groups cannot be empty"

ifaceToSig :: Interface -> Sig
ifaceToSig (Interface name args) = Sig (T.pack name) (fmap fromdecl args)
  where
    fromdecl (Decl t _) = t

translateBehv :: ContractMap -> Behaviour -> ActM (EVM.Expr EVM.End)
translateBehv cmap (Behaviour _ _ _ preconds caseconds _ upds ret) = do
  fresh <- getFresh
  preconds' <- mapM (toProp cmap) preconds
  caseconds' <- mapM (toProp cmap) caseconds
  ret' <- returnsToExpr cmap ret
  store <- applyUpdates cmap cmap upds
  fresh' <- getFresh
  pure $ EVM.Success (preconds' <> caseconds' <> symAddrCnstr (fresh+1) fresh') mempty ret' store


applyUpdates :: ContractMap -> ContractMap -> [StorageUpdate] -> ActM ContractMap
applyUpdates readMap writeMap upds = foldM (applyUpdate readMap) writeMap upds

applyUpdate :: ContractMap -> ContractMap -> StorageUpdate -> ActM ContractMap
applyUpdate readMap writeMap (Update typ (Item _ _ ref) e) = do
  caddr' <- baseAddr readMap ref
  offset <- refOffset readMap ref
  let contract = fromMaybe (error $ "Internal error: contract not found\n" <> show e) $ M.lookup caddr' writeMap
  case typ of
    SInteger -> do
      e' <- toExpr readMap e
      pure $ M.insert caddr' (updateStorage (EVM.SStore offset e') contract) writeMap
    SBoolean -> do
      e' <- toExpr readMap e
      pure $ M.insert caddr' (updateStorage (EVM.SStore offset e') contract) writeMap
    SByteStr -> error "Bytestrings not supported"
    SContract -> case e of
     Create _ _ _ -> do
       fresh <- getFreshIncr
       let freshAddr = EVM.SymAddr $ "freshSymAddr" <> (T.pack $ show fresh)
       writeMap' <- localCaddr freshAddr $ createContract readMap writeMap freshAddr e
       pure $ M.insert caddr' (updateNonce (updateStorage (EVM.SStore offset (EVM.WAddr freshAddr)) contract)) writeMap'
     AsContract _ (Var _ _ _ x) _ -> do
       let e' = EVM.WAddr (EVM.SymAddr $ T.pack x)
       pure $ M.insert caddr' (updateStorage (EVM.SStore offset e') contract) writeMap
     AsContract _ _ _ -> error "Casting only allowed in variables"
     _ -> error "Contractor call or casting expected"
  where

    updateStorage :: (EVM.Expr EVM.Storage -> EVM.Expr EVM.Storage) -> EVM.Expr EVM.EContract -> EVM.Expr EVM.EContract
    updateStorage updfun (EVM.C code storage bal nonce) = EVM.C code (updfun storage) bal nonce
    updateStorage _ (EVM.GVar _) = error "Internal error: contract cannot be a global variable"

    updateNonce :: EVM.Expr EVM.EContract -> EVM.Expr EVM.EContract
    updateNonce (EVM.C code storage bal (Just n)) = EVM.C code storage bal (Just (n + 1))
    updateNonce c@(EVM.C _ _ _ Nothing) = c
    updateNonce (EVM.GVar _) = error "Internal error: contract cannot be a global variable"

createContract :: ContractMap -> ContractMap -> EVM.Expr EVM.EAddr -> Exp AContract -> ActM ContractMap
createContract readMap writeMap freshAddr (Create _ cid args) = do
  codemap <- getCodemap
  case M.lookup cid codemap of
    Just (Contract (Constructor _ iface _ _ _ upds) _, _, bytecode) -> do
      let contract = EVM.C { EVM.code  = EVM.RuntimeCode (EVM.ConcreteRuntimeCode bytecode)
                           , EVM.storage = EVM.ConcreteStore mempty
                           , EVM.balance = EVM.Lit 0
                           , EVM.nonce = Just 1
                           }
      let subst = makeSubstMap iface args

      let upds' = substUpds subst upds
      applyUpdates (M.insert freshAddr contract readMap) (M.insert freshAddr contract writeMap) upds'
    Nothing -> error "Internal error: constructor not found"
createContract _ _ _ _ = error "Internal error: constructor call expected"

-- | Substitutions

makeSubstMap :: Interface -> [TypedExp] -> M.Map Id TypedExp
makeSubstMap (Interface _ decls) args =
  M.fromList $ zipWith (\(Decl _ x) texp -> (x, texp)) decls args

substUpds :: M.Map Id TypedExp -> [StorageUpdate] -> [StorageUpdate]
substUpds subst upds = fmap (substUpd subst) upds

substUpd :: M.Map Id TypedExp -> StorageUpdate -> StorageUpdate
substUpd subst (Update s item expr) = Update s (substItem subst item) (substExp subst expr)

substItem :: M.Map Id TypedExp -> TStorageItem a -> TStorageItem a
substItem subst (Item st vt sref) = Item st vt (substStorageRef subst sref)

substStorageRef :: M.Map Id TypedExp -> StorageRef -> StorageRef
substStorageRef _ var@(SVar _ _ _) = var
substStorageRef subst (SMapping pn sref args) = SMapping pn (substStorageRef subst sref) (substArgs subst args)
substStorageRef subst (SField pn sref x y) = SField pn (substStorageRef subst sref) x y

substArgs :: M.Map Id TypedExp -> [TypedExp] -> [TypedExp]
substArgs subst exps = fmap (substTExp subst) exps

substTExp :: M.Map Id TypedExp -> TypedExp -> TypedExp
substTExp subst (TExp st expr) = TExp st (substExp subst expr)

substExp :: M.Map Id TypedExp -> Exp a -> Exp a
substExp subst expr = case expr of
  And pn a b -> And pn (substExp subst a) (substExp subst b)
  Or pn a b -> Or pn (substExp subst a) (substExp subst b)
  Impl pn a b -> Impl pn (substExp subst a) (substExp subst b)
  Neg pn a -> Neg pn (substExp subst a)
  LT pn a b -> LT pn (substExp subst a) (substExp subst b)
  LEQ pn a b -> LEQ pn (substExp subst a) (substExp subst b)
  GEQ pn a b -> GEQ pn (substExp subst a) (substExp subst b)
  GT pn a b -> GT pn (substExp subst a) (substExp subst b)
  LitBool _ _ -> expr

  Add pn a b -> Add pn (substExp subst a) (substExp subst b)
  Sub pn a b -> Sub pn (substExp subst a) (substExp subst b)
  Mul pn a b -> Mul pn (substExp subst a) (substExp subst b)
  Div pn a b -> Div pn (substExp subst a) (substExp subst b)
  Mod pn a b -> Mod pn (substExp subst a) (substExp subst b)
  Exp pn a b -> Exp pn (substExp subst a) (substExp subst b)
  LitInt _ _ -> expr
  IntEnv _ _ -> expr

  IntMin _ _ -> expr
  IntMax _ _ -> expr
  UIntMin _ _ -> expr
  UIntMax _ _ -> expr
  InRange pn t a -> InRange pn t (substExp subst a)

  Cat pn a b -> Cat pn (substExp subst a) (substExp subst b)
  Slice pn a b c -> Slice pn (substExp subst a) (substExp subst b) (substExp subst c)
  ByStr _ _ -> expr
  ByLit _ _ -> expr
  ByEnv _ _ -> expr

  Eq pn st a b -> Eq pn st (substExp subst a) (substExp subst b)
  NEq pn st a b -> NEq pn st (substExp subst a) (substExp subst b)

  ITE pn a b c -> ITE pn (substExp subst a) (substExp subst b) (substExp subst c)
  TEntry _ _ _ -> expr
  Var _ st _ x -> case M.lookup x subst of
    Just (TExp st' exp') -> maybe (error "Internal error: type missmatch") (\Refl -> exp') $ testEquality st st'
    Nothing -> expr

  Create pn a b -> Create pn a (substArgs subst b)
  AsContract {} -> error "Calling contracts with casting not supported yet"


returnsToExpr :: ContractMap -> Maybe TypedExp -> ActM (EVM.Expr EVM.Buf)
returnsToExpr _ Nothing = pure $ EVM.ConcreteBuf ""
returnsToExpr cmap (Just r) = typedExpToBuf cmap r

wordToBuf :: EVM.Expr EVM.EWord -> EVM.Expr EVM.Buf
wordToBuf w = EVM.WriteWord (EVM.Lit 0) w (EVM.ConcreteBuf "")

wordToProp :: EVM.Expr EVM.EWord -> EVM.Prop
wordToProp w = EVM.PNeg (EVM.PEq w (EVM.Lit 0))

typedExpToBuf :: ContractMap -> TypedExp -> ActM (EVM.Expr EVM.Buf)
typedExpToBuf cmap expr =
  case expr of
    TExp styp e -> expToBuf cmap styp e

expToBuf :: forall a. ContractMap -> SType a -> Exp a  -> ActM (EVM.Expr EVM.Buf)
expToBuf cmap styp e = do
  case styp of
    SInteger -> do
      e' <- toExpr cmap e
      pure $ EVM.WriteWord (EVM.Lit 0) e' (EVM.ConcreteBuf "")
    SBoolean -> do
      e' <- toExpr cmap e
      pure $ EVM.WriteWord (EVM.Lit 0) e' (EVM.ConcreteBuf "")
    SByteStr -> toExpr cmap e
    SContract -> error "Internal error: expecting primitive type"

getSlot :: Layout -> Id -> Id -> Integer
getSlot layout cid name =
  case M.lookup cid layout of
    Just m -> case M.lookup name m of
      Just v -> v
      Nothing -> error $ "Internal error: invalid variable name: " <> show name
    Nothing -> error "Internal error: invalid contract name"

refOffset :: ContractMap -> StorageRef -> ActM (EVM.Expr EVM.EWord)
refOffset _ (SVar _ cid name) = do
  layout <- getLayout
  let slot = getSlot layout cid name
  pure $ EVM.Lit (fromIntegral slot)
refOffset cmap (SMapping _ ref ixs) = do
  slot <- refOffset cmap ref
  foldM (\slot' i -> do
            buf <- typedExpToBuf cmap i
            pure (EVM.keccak (buf <> (wordToBuf slot')))) slot ixs
refOffset _ (SField _ _ cid name) = do
  layout <- getLayout
  let slot = getSlot layout cid name
  pure $ EVM.Lit (fromIntegral slot)

baseAddr :: ContractMap -> StorageRef -> ActM (EVM.Expr EVM.EAddr)
baseAddr _ (SVar _ _ _) = getCaddr
baseAddr cmap (SField _ ref _ _) = refAddr cmap ref
baseAddr cmap (SMapping _ ref _) = baseAddr cmap ref

-- | find the contract that is stored in the given reference of contract type
refAddr :: ContractMap -> StorageRef -> ActM (EVM.Expr EVM.EAddr)
refAddr cmap (SVar _ c x) = do
  caddr <- getCaddr
  case M.lookup caddr cmap of
    Just (EVM.C _ storage _ _) -> do
      layout <- getLayout
      let slot = EVM.Lit $ fromIntegral $ getSlot layout c x
      case simplify (EVM.SLoad slot storage) of
        EVM.WAddr symaddr -> pure symaddr
        _ -> error $ "Internal error: did not find a symbolic address"
    Just _ -> error "Internal error: unepected GVar "
    Nothing -> error "Internal error: contract not found"
refAddr cmap (SField _ ref c x) = do
  layout <- getLayout
  caddr' <- refAddr cmap ref
  case M.lookup caddr' cmap of
    Just (EVM.C _ storage _ _) -> do
      let slot = EVM.Lit $ fromIntegral $ getSlot layout c x
      case simplify (EVM.SLoad slot storage) of
        EVM.WAddr symaddr -> pure symaddr
        _ -> error "Internal error: did not find a symbolic address"
    Just _ -> error "Internal error: unepected GVar "
    Nothing -> error "Internal error: contract not found"
refAddr _ (SMapping _ _ _) = error "Internal error: mapping address not suppported"

ethEnvToWord :: EthEnv -> ActM (EVM.Expr EVM.EWord)
ethEnvToWord Callvalue = pure $ EVM.TxValue
ethEnvToWord Caller = do
  c <- getCaller
  pure $ EVM.WAddr c
ethEnvToWord Origin = pure $ EVM.WAddr (EVM.SymAddr "origin") -- Why not: pure $ EVM.Origin
ethEnvToWord Blocknumber = pure $ EVM.BlockNumber
ethEnvToWord Blockhash = pure $ EVM.BlockHash $ EVM.Lit 0
ethEnvToWord Chainid = pure $ EVM.ChainId
ethEnvToWord Gaslimit = pure $ EVM.GasLimit
ethEnvToWord Coinbase = pure $ EVM.Coinbase
ethEnvToWord Timestamp = pure $ EVM.Timestamp
ethEnvToWord This = do
  c <- getCaddr
  pure $ EVM.WAddr c
ethEnvToWord Nonce = error "TODO"
ethEnvToWord Calldepth = error "TODO"
ethEnvToWord Difficulty = error "TODO"

ethEnvToBuf :: EthEnv -> EVM.Expr EVM.Buf
ethEnvToBuf _ = error "Internal error: there are no bytestring environment values"


toProp :: ContractMap -> Exp ABoolean -> ActM EVM.Prop
toProp cmap = \case
  (And _ e1 e2) -> pop2 EVM.PAnd e1 e2
  (Or _ e1 e2) -> pop2 EVM.POr e1 e2
  (Impl _ e1 e2) -> pop2 EVM.PImpl e1 e2
  (Neg _ e1) -> do
    e1' <- toProp cmap e1
    pure $ EVM.PNeg e1'
  (Act.LT _ e1 e2) -> op2 EVM.PLT e1 e2
  (LEQ _ e1 e2) -> op2 EVM.PLEq e1 e2
  (GEQ _ e1 e2) -> op2 EVM.PGEq e1 e2
  (Act.GT _ e1 e2) -> op2 EVM.PGT e1 e2
  (LitBool _ b) -> pure $ EVM.PBool b
  (Eq _ SInteger e1 e2) -> op2 EVM.PEq e1 e2
  (Eq _ SBoolean e1 e2) -> op2 EVM.PEq e1 e2
  (Eq _ _ _ _) -> error "unsupported"
  (NEq _ SInteger e1 e2) -> do
    e <- op2 EVM.PEq e1 e2
    pure $ EVM.PNeg e
  (NEq _ SBoolean e1 e2) -> do
    e <- op2 EVM.PEq e1 e2
    pure $ EVM.PNeg e
  (NEq _ _ _ _) -> error "unsupported"
  (ITE _ _ _ _) -> error "Internal error: expecting flat expression"
  (Var _ _ _ _) -> error "TODO"
  (TEntry _ _ _) -> error "TODO" -- EVM.SLoad addr idx
  (InRange _ t e) -> toProp cmap (inRange t e)
  where
    op2 :: forall a b. (EVM.Expr (ExprType b) -> EVM.Expr (ExprType b) -> a) -> Exp b -> Exp b -> ActM a
    op2 op e1 e2 = do
      e1' <- toExpr cmap e1
      e2' <- toExpr cmap e2
      pure $ op e1' e2'

    pop2 :: forall a. (EVM.Prop -> EVM.Prop -> a) -> Exp ABoolean -> Exp ABoolean -> ActM a
    pop2 op e1 e2 = do
      e1' <- toProp cmap e1
      e2' <- toProp cmap e2
      pure $ op e1' e2'

pattern MAX_UINT :: EVM.W256
pattern MAX_UINT = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

-- TODO: this belongs in HEVM
stripMods :: EVM.Expr a -> EVM.Expr a
stripMods = mapExpr go
  where
    go :: EVM.Expr a -> EVM.Expr a
    go (EVM.Mod a (EVM.Lit MAX_UINT)) = a
    go a = a

toExpr :: forall a. ContractMap -> Exp a -> ActM (EVM.Expr (ExprType a))
toExpr cmap = liftM stripMods . go
  where
    go = \case
      -- booleans
      (And _ e1 e2) -> op2 EVM.And e1 e2
      (Or _ e1 e2) -> op2 EVM.Or e1 e2
      (Impl _ e1 e2) -> op2 (\x y -> EVM.Or (EVM.Not x) y) e1 e2
      (Neg _ e1) -> do
        e1' <- toExpr cmap e1
        pure $ EVM.Not e1'
      (Act.LT _ e1 e2) -> op2 EVM.LT e1 e2
      (LEQ _ e1 e2) -> op2 EVM.LEq e1 e2
      (GEQ _ e1 e2) -> op2 EVM.GEq e1 e2
      (Act.GT _ e1 e2) -> op2 EVM.GT e1 e2
      (LitBool _ b) -> pure $ EVM.Lit (fromIntegral $ fromEnum $ b)
      -- integers
      (Add _ e1 e2) -> op2 EVM.Add e1 e2
      (Sub _ e1 e2) -> op2 EVM.Sub e1 e2
      (Mul _ e1 e2) -> op2 EVM.Mul e1 e2
      (Div _ e1 e2) -> op2 EVM.Div e1 e2
      (Mod _ e1 e2) -> op2 EVM.Mod e1 e2 -- which mod?
      (Exp _ e1 e2) -> op2 EVM.Exp e1 e2
      (LitInt _ n) -> pure $ EVM.Lit (fromIntegral n)
      (IntEnv _ env) -> ethEnvToWord env
      -- bounds
      (IntMin _ n) -> pure $ EVM.Lit (fromIntegral $ intmin n)
      (IntMax _ n) -> pure $ EVM.Lit (fromIntegral $ intmax n)
      (UIntMin _ n) -> pure $ EVM.Lit (fromIntegral $ uintmin n)
      (UIntMax _ n) -> pure $ EVM.Lit (fromIntegral $ uintmax n)
      (InRange _ t e) -> toExpr cmap (inRange t e)
      -- bytestrings
      (Cat _ _ _) -> error "TODO"
      (Slice _ _ _ _) -> error "TODO"
      -- EVM.CopySlice (toExpr start) (EVM.Lit 0) -- src and dst offset
      -- (EVM.Add (EVM.Sub (toExp end) (toExpr start)) (EVM.Lit 0)) -- size
      -- (toExpr bs) (EVM.ConcreteBuf "") -- src and dst
      (ByStr _ str) -> pure $  EVM.ConcreteBuf (B8.pack str)
      (ByLit _ bs) -> pure $ EVM.ConcreteBuf bs
      (ByEnv _ env) -> pure $ ethEnvToBuf env
      -- contracts
      (Create _ _ _) -> error "internal error: Create calls not supported in this context"
      -- polymorphic
      (Eq _ SInteger e1 e2) -> op2 EVM.Eq e1 e2
      (Eq _ SBoolean e1 e2) -> op2 EVM.Eq e1 e2
      (Eq _ _ _ _) -> error "unsupported"

      (NEq _ SInteger e1 e2) -> do
        e <- op2 EVM.Eq e1 e2
        pure $ EVM.Not $ e
      (NEq _ SBoolean e1 e2) -> do
        e <- op2 EVM.Eq e1 e2
        pure $ EVM.Not $ e
      (NEq _ _ _ _) -> error "unsupported"

      e@(ITE _ _ _ _) -> error $ "Internal error: expecting flat expression. got: " <> show e
      (Var _ SInteger typ x) ->  -- TODO other types
        pure $ fromCalldataFramgment $ symAbiArg (T.pack x) typ

      (TEntry _ _ (Item SInteger _ ref)) -> do
        slot <- refOffset cmap ref
        caddr' <- baseAddr cmap ref
        let contract = fromMaybe (error "Internal error: contract not found") $ M.lookup caddr' cmap
        let storage = case contract of
                        EVM.C _ s _ _  -> s
                        EVM.GVar _ -> error "Internal error: contract cannot be a global variable"
        pure $ EVM.SLoad slot storage

      e ->  error $ "TODO: " <> show e

    op2 :: forall b c. (EVM.Expr (ExprType c) -> EVM.Expr (ExprType c) -> b) -> Exp c -> Exp c -> ActM b
    op2 op e1 e2 = do
      e1' <- toExpr cmap e1
      e2' <- toExpr cmap e2
      pure $ op e1' e2'

    fromCalldataFramgment :: CalldataFragment -> EVM.Expr EVM.EWord
    fromCalldataFramgment (St _ word) = word
    fromCalldataFramgment _ = error "Internal error: only static types are supported"

inRange :: AbiType -> Exp AInteger -> Exp ABoolean
-- if the type has the type of machine word then check per operation
inRange (AbiUIntType 256) e = checkOp e
inRange (AbiIntType 256) _ = error "TODO signed integers"
-- otherwise insert range bounds
inRange t e = bound t e


checkOp :: Exp AInteger -> Exp ABoolean
checkOp (LitInt _ i) = LitBool nowhere $ i <= (fromIntegral (maxBound :: Word256))
checkOp (Var _ _ _ _)  = LitBool nowhere True
checkOp (TEntry _ _ _)  = LitBool nowhere True
checkOp e@(Add _ e1 _) = LEQ nowhere e1 e -- check for addition overflow
checkOp e@(Sub _ e1 _) = LEQ nowhere e e1
checkOp (Mul _ e1 e2) = Or nowhere (Eq nowhere SInteger e1 (LitInt nowhere 0))
                          (Impl nowhere (NEq nowhere SInteger e1 (LitInt nowhere 0))
                            (Eq nowhere SInteger e2 (Div nowhere (Mul nowhere e1 e2) e1)))
checkOp (Div _ _ _) = LitBool nowhere True
checkOp (Mod _ _ _) = LitBool nowhere True
checkOp (Exp _ _ _) = error "TODO check for exponentiation overflow"
checkOp (IntMin _ _)  = error "Internal error: invalid in range expression"
checkOp (IntMax _ _)  = error "Internal error: invalid in range expression"
checkOp (UIntMin _ _) = error "Internal error: invalid in range expression"
checkOp (UIntMax _ _) = error "Internal error: invalid in range expression"
checkOp (ITE _ _ _ _) = error "Internal error: invalid in range expression"
checkOp (IntEnv _ _) = error "Internal error: invalid in range expression"


-- * Equivalence checking


-- | Wrapper for the equivalenceCheck function of hevm
checkEquiv :: App m => SolverGroup -> [EVM.Expr EVM.End] -> [EVM.Expr EVM.End] -> m [EquivResult]
checkEquiv solvers l1 l2 = do
  res <- equivalenceCheck' solvers l1 l2
  pure $ fmap toEquivRes res
  where
    toEquivRes :: SymExec.EquivResult -> EquivResult
    toEquivRes (Cex cex) = Cex ("\x1b[1mThe following input results in different behaviours\x1b[m", cex)
    toEquivRes (Qed a) = Qed a
    toEquivRes (Timeout b) = Timeout b



getInitContractMap :: [(Exp AInteger, Id)] -> Store -> CodeMap -> (ContractMap, [(EVM.Expr EVM.EAddr, EVM.Contract)], Int)
getInitContractMap casts store codemap =
  -- TODO check that there is no aliasing in the casted addresses and that contracts have no casting
  let casts' = groupBy (\x y -> fst x == fst y) casts in
  let (cmap, fresh) =  foldl (\p l -> handleCast p (nub l)) (M.empty, 0) casts' in
  let (actstorage, hevmstorage) = createStorage cmap in
  (actstorage, hevmstorage, fresh)
  
  where
    handleCast :: (ContractMap, Int) -> [(Exp AInteger, Id)] -> (ContractMap, Int)
    handleCast (cmap, fresh) [(Var _ _ _ x, cid)] =
      let addr = EVM.SymAddr $ T.pack x in
      let actenv = ActEnv codemap fresh (slotMap store) addr Nothing in
      case M.lookup cid codemap of
        Just (Contract (Constructor _ _ _ _ _ upds) _, _, bytecode) ->
          let (actstorage, _) = createStorage cmap in
          let contract = EVM.C { EVM.code  = EVM.RuntimeCode (EVM.ConcreteRuntimeCode bytecode)
                               , EVM.storage = EVM.ConcreteStore mempty
                               , EVM.balance = EVM.Lit 0
                               , EVM.nonce = Just 1
                               } in
          let (cmap', actenv') = flip runState actenv $ applyUpdates (M.insert addr contract actstorage) (M.insert addr contract actstorage) upds in
          (cmap', actenv'.fresh)
        Nothing -> error $ "Internal error: Contract " <> cid <> " not found\n" <> show codemap
    handleCast _ [(_, _)] = error "Only casts to symbolic arguments are allowed"
    handleCast _ [] = error "Internal error: Cast cannot be empty"
    handleCast _ _ = error "Cannot have different casts to the same address"
  

checkConstructors :: App m => SolverGroup -> ByteString -> ByteString -> Store -> Contract -> CodeMap -> m (Error String (ContractMap, ActEnv))
checkConstructors solvers initcode runtimecode store (Contract ctor _) codemap = do
  -- First find all casts from addresses and create a store where all asumed constracts are present
  -- currently ignoring any asts in behaviours, maybe prohibit them explicitly
  let casts = castsFromConstructor ctor
  let (actinitmap, hevminitmap, fresh) = getInitContractMap casts store codemap
  -- Create the Act state
  let actenv = ActEnv codemap fresh (slotMap store) (EVM.SymAddr "entrypoint") Nothing
  -- Translate Act constructor to Expr
  let ((actbehvs, calldata, sig), actenv') = flip runState actenv $ translateConstructor runtimecode ctor actinitmap
  -- check is any addresses casted to contracts can be aliased
  checkAliasing solvers ctor (map fst casts) calldata
  -- Symbolically execute bytecode  
  solbehvs <- removeFails <$> getInitcodeBranches solvers initcode hevminitmap calldata (symAddrCnstr 1 fresh) fresh
  
  -- traceM "Solc behvs: "
  -- traceM $ showBehvs solbehvs
  -- traceM "Act behvs: "
  -- traceM $ showBehvs actbehvs

  -- Check equivalence
  showMsg "\x1b[1mChecking if constructor results are equivalent.\x1b[m"
  res1 <- checkResult calldata (Just sig) =<< checkEquiv solvers solbehvs actbehvs
  showMsg "\x1b[1mChecking if constructor input spaces are the same.\x1b[m"
  res2 <- checkResult calldata (Just sig) =<< checkInputSpaces solvers solbehvs actbehvs
  pure $ res1 *> res2 *> Success (getContractMap actbehvs, actenv')
  where
    removeFails branches = filter isSuccess $ branches

getContractMap :: [EVM.Expr EVM.End] -> ContractMap
getContractMap [EVM.Success _ _ _ m] = m
getContractMap _ = error "Internal error: unexpected shape of Act translation"

checkBehaviours :: forall m. App m => SolverGroup -> Contract -> ActEnv -> ContractMap -> m (Error String ())
checkBehaviours solvers (Contract _ behvs) actenv cmap = do
  let (actstorage, hevmstorage) = createStorage cmap
  let actbehvs = fst $ flip runState actenv $ translateBehvs actstorage behvs
  (liftM $ concatError def) $ flip mapM actbehvs $ \(name,behvs',calldata, sig) -> do
    solbehvs <- removeFails <$> getRuntimeBranches solvers hevmstorage calldata actenv.fresh
    showMsg $ "\x1b[1mChecking behavior \x1b[4m" <> name <> "\x1b[m of Act\x1b[m"
    -- equivalence check
    showMsg $ "\x1b[1mChecking if behaviour is matched by EVM\x1b[m"
    res1 <- checkResult calldata (Just sig) =<< checkEquiv solvers solbehvs behvs'
    -- input space exhaustiveness check
    showMsg $ "\x1b[1mChecking if the input spaces are the same\x1b[m"
    res2 <- checkResult calldata (Just sig) =<< checkInputSpaces solvers solbehvs behvs'
    pure $ res1 *> res2

  where
    removeFails branches = filter isSuccess $ branches
    def = Success ()

createStorage :: ContractMap -> (ContractMap, [(EVM.Expr EVM.EAddr, EVM.Contract)])
createStorage cmap =
  let cmap' = M.mapWithKey makeContract cmap in
  let contracts = fmap (\(addr, c) -> (addr, toContract c)) $ M.toList cmap' in
  (cmap', contracts)

  where
    traverseStorage ::  EVM.Expr EVM.EAddr -> EVM.Expr EVM.Storage -> EVM.Expr EVM.Storage
    traverseStorage addr (EVM.SStore offset (EVM.WAddr symaddr) storage) =
      EVM.SStore offset (EVM.WAddr symaddr) (traverseStorage addr storage)
    traverseStorage addr (EVM.SStore _ _ storage) = traverseStorage addr storage
    traverseStorage addr (EVM.ConcreteStore _) = EVM.AbstractStore addr Nothing
    traverseStorage _ s@(EVM.AbstractStore {}) = s
    traverseStorage _ _ = error $ "Internal error: unexpected storage shape"

    makeContract :: EVM.Expr EVM.EAddr -> EVM.Expr EVM.EContract -> EVM.Expr EVM.EContract
    makeContract addr (EVM.C code storage _ _) = EVM.C code (traverseStorage addr storage) (EVM.Balance addr) (Just 0)
    makeContract _ (EVM.GVar _) = error "Internal error: contract cannot be gvar"

    toContract :: EVM.Expr EVM.EContract -> EVM.Contract
    toContract (EVM.C code storage balance nonce) = EVM.Contract
      { EVM.code        = code
      , EVM.storage     = storage
      , EVM.origStorage = storage
      , EVM.balance     = balance
      , EVM.nonce       = nonce
      , EVM.codehash    = EVM.hashcode code
      , EVM.opIxMap     = EVM.mkOpIxMap code
      , EVM.codeOps     = EVM.mkCodeOps code
      , EVM.external    = False
      }
    toContract (EVM.GVar _) = error "Internal error: contract cannot be gvar"


-- | Find the input space of an expr list
inputSpace :: [EVM.Expr EVM.End] -> [EVM.Prop]
inputSpace exprs = map aux exprs
  where
    aux :: EVM.Expr EVM.End -> EVM.Prop
    aux (EVM.Success c _ _ _) = EVM.pand c
    aux _ = error "List should only contain success behaviours"

-- | Check whether two lists of behaviours cover exactly the same input space
checkInputSpaces :: App m => SolverGroup -> [EVM.Expr EVM.End] -> [EVM.Expr EVM.End] -> m [EquivResult]
checkInputSpaces solvers l1 l2 = do
  let p1 = inputSpace l1
  let p2 = inputSpace l2
  conf <- readConfig

  let queries = fmap (assertProps conf) [ [ EVM.PNeg (EVM.por p1), EVM.por p2 ]
                                        , [ EVM.por p1, EVM.PNeg (EVM.por p2) ] ]

  results <- liftIO $ mapConcurrently (checkSat solvers) queries
  let results' = case results of
                   [r1, r2] -> [ toVRes "\x1b[1mThe following inputs are accepted by Act but not EVM\x1b[m" r1
                               , toVRes "\x1b[1mThe following inputs are accepted by EVM but not Act\x1b[m" r2 ]
                   _ -> error "Internal error: impossible"

  case all isQed results' of
    True -> pure [Qed ()]
    False -> pure $ filter (/= Qed ()) results'


-- Checks that all the casted addresses of a contract are mutually distinct
checkAliasing :: App m => SolverGroup -> Constructor -> [Exp AInteger] -> Calldata -> m (Error String ())
checkAliasing solver constructor@(Constructor _ (Interface ifaceName decls) preconds _ _ _) addresses@(_:_) calldata = do
  let addressquery = [prelude <> SMT2 (fmap fromString $ lines . show . prettyAnsi $ mksmt) mempty mempty mempty]
  traceShowM addressquery
  res <- liftIO $ mapConcurrently (checkSat solver) addressquery
  checkResult calldata Nothing (fmap (toVRes msg) res)
  where
    -- declare vars
    args = SMT.declareArg ifaceName <$> decls
    envs = SMT.declareEthEnv <$> ethEnvFromConstructor constructor
    -- constraints
    asserts = SMT.mkAssert ifaceName <$> ((existEqual (combine addresses [])):preconds)    
    mksmt = SMT.SMTExp
      { SMT._storage = []
      , SMT._calldata = args
      , SMT._environment = envs
      , SMT._assertions = asserts
      }

    combine :: [Exp AInteger] -> [[(Exp AInteger,Exp AInteger)]] -> [(Exp AInteger,Exp AInteger)]
    combine [] acc = concat acc
    combine (x:xs) acc = combine xs ([(x,y) | y <- xs]:acc) 

    existEqual :: [(Exp AInteger,Exp AInteger)] -> Exp ABoolean
    existEqual ls = foldl (\p (x,y) -> Or nowhere (Eq nowhere SInteger x y) p) (LitBool nowhere False) ls

    msg = "\x1b[1m Input addresses are not guaranteed to be unique!\x1b[m"

    prelude :: SMT2
    prelude =  SMT2 src mempty mempty mempty
      where
        src = [ "; logic",
                "; this is a test",
                "(set-info :smt-lib-version 2.6)",
                "(set-logic ALL)" ]


checkAliasing _ _ _ _ = pure $ Success ()

-- | Checks whether all successful EVM behaviors are withing the
-- interfaces specified by Act
checkAbi :: App m => SolverGroup -> Contract -> ContractMap -> m (Error String ())
checkAbi solver contract cmap = do
  showMsg "\x1b[1mChecking if the ABI of the contract matches the specification\x1b[m"
  let (_, hevmstorage) = createStorage cmap
  let txdata = EVM.AbstractBuf "txdata"
  let selectorProps = assertSelector txdata <$> nubOrd (actSigs contract)
  evmBehvs <- getRuntimeBranches solver hevmstorage (txdata, []) 0 -- TODO what freshAddr goes here?
  conf <- readConfig
  let queries =  fmap (assertProps conf) $ filter (/= []) $ fmap (checkBehv selectorProps) evmBehvs
  res <- liftIO $ mapConcurrently (checkSat solver) queries
  checkResult (txdata, []) Nothing (fmap (toVRes msg) res)

  where
    actSig (Behaviour _ _ iface _ _ _ _ _) = T.pack $ makeIface iface
    actSigs (Contract _ behvs) = actSig <$> behvs

    checkBehv :: [EVM.Prop] -> EVM.Expr EVM.End -> [EVM.Prop]
    checkBehv assertions (EVM.Success cnstr _ _ _) = assertions <> cnstr
    checkBehv _ (EVM.Failure _ _ _) = []
    checkBehv _ (EVM.Partial _ _ _) = []
    checkBehv _ (EVM.ITE _ _ _) = error "Internal error: HEVM behaviours must be flattened"
    checkBehv _ (EVM.GVar _) = error "Internal error: unepected GVar"

    msg = "\x1b[1mThe following function selector results in behaviors not covered by the Act spec:\x1b[m"

checkContracts :: forall m. App m => SolverGroup -> Store -> M.Map Id (Contract, BS.ByteString, BS.ByteString) -> m (Error String ())
checkContracts solvers store codemap =
  liftM (concatError def) $ flip mapM (M.toList codemap) (\(_, (contract, initcode, bytecode)) -> do
    showMsg $ "\x1b[1mChecking contract \x1b[4m" <> nameOfContract contract <> "\x1b[m"
    res <- checkConstructors solvers initcode bytecode store contract codemap
    case res of
      Success (cmap, actenv) -> do
        behs <- checkBehaviours solvers contract actenv cmap
        abi <- checkAbi solvers contract cmap
        pure $ behs *> abi
      Failure e -> pure $ Failure e)
  where
    def = Success ()


readSelector :: EVM.Expr EVM.Buf -> EVM.Expr EVM.EWord
readSelector txdata =
    EVM.JoinBytes (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.ReadByte (EVM.Lit 0x0) txdata)
                  (EVM.ReadByte (EVM.Lit 0x1) txdata)
                  (EVM.ReadByte (EVM.Lit 0x2) txdata)
                  (EVM.ReadByte (EVM.Lit 0x3) txdata)


assertSelector ::  EVM.Expr EVM.Buf -> T.Text -> EVM.Prop
assertSelector txdata sig =
  EVM.PNeg (EVM.PEq sel (readSelector txdata))
  where
    sel = EVM.Lit $ fromIntegral $ (EVM.abiKeccak (encodeUtf8 sig)).unFunctionSelector


-- * Utils

toVRes :: T.Text -> CheckSatResult -> EquivResult
toVRes msg res = case res of
  Sat cex -> Cex (msg, cex)
  EVM.Solvers.Unknown -> Timeout ()
  Unsat -> Qed ()
  Error e -> error $ "Internal Error: solver responded with error: " <> show e


checkResult :: App m => Calldata -> Maybe Sig -> [EquivResult] -> m (Error String ())
checkResult calldata sig res =
  case any isCex res of
    False ->
      case any isTimeout res of
        True -> do
          showMsg "\x1b[41mNo discrepancies found but timeout(s) occurred. \x1b[m"
          pure $ Failure $ NE.singleton (nowhere, "Failure: Cannot prove equivalence.")
        False -> do
          showMsg "\x1b[42mNo discrepancies found.\x1b[m "
          pure $ Success ()
    True -> do
      let cexs = mapMaybe getCex res
      showMsg $ T.unpack . T.unlines $ [ "\x1b[41mNot equivalent.\x1b[m", "" , "-----", ""] <> (intersperse (T.unlines [ "", "-----" ]) $ fmap (\(msg, cex) -> msg <> "\n" <> formatCex (fst calldata) sig cex) cexs)
      pure $ Failure $ NE.singleton (nowhere, "Failure: Cannot prove equivalence.")

-- | Pretty prints a list of hevm behaviours for debugging purposes
showBehvs :: [EVM.Expr a] -> String
showBehvs behvs = T.unpack $ T.unlines $ fmap Format.formatExpr behvs

showProps :: [EVM.Prop] -> String
showProps props = T.unpack $ T.unlines $ fmap Format.formatProp props
