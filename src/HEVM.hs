{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeApplications #-}


module HEVM where

import Prelude hiding (GT, LT)

import qualified Data.Map as M
import Data.List
import Data.Containers.ListUtils (nubOrd)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Text.Lazy.IO as TL
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8 (pack)
import Data.Text.Encoding (encodeUtf8)
import Control.Concurrent.Async
import Control.Monad
import Data.DoubleWord
import Data.Maybe
import System.Exit ( exitFailure )
import Control.Monad.ST (stToIO)
import Data.Type.Equality (TestEquality(..), (:~:)(..))

import Syntax.Annotated
import Syntax.Untyped (makeIface)
import Syntax

import qualified EVM.Types as EVM hiding (Contract(..))
import EVM.Expr hiding (op2, inRange)
import EVM.SymExec hiding (EquivResult, isPartial)
import qualified EVM.SymExec as SymExec (EquivResult)
import EVM.SMT (SMTCex(..), assertProps, formatSMT2)
import EVM.Solvers
import qualified EVM.Format as Format
import qualified EVM.Fetch as Fetch

import Debug.Trace

type family ExprType a where
  ExprType 'AInteger  = EVM.EWord
  ExprType 'ABoolean  = EVM.EWord
  ExprType 'AByteStr  = EVM.Buf
  ExprType 'AContract = EVM.EWord -- address?

type Layout = M.Map Id (M.Map Id Integer)

-- TODO move this to HEVM
type Calldata = (EVM.Expr EVM.Buf, [EVM.Prop])

type ContractMap = M.Map (EVM.Expr EVM.EAddr) (EVM.Expr EVM.EContract)

-- | For each contract in the Act spec, put in a codemap its Act
-- specification, init code, and runtimecode. This is being looked up
-- when we encounter a constructor call.
type CodeMap = M.Map Id (Contract, BS.ByteString, BS.ByteString)

type EquivResult = ProofResult () (T.Text, SMTCex) ()

abstRefineDefault :: EVM.AbstRefineConfig
abstRefineDefault = EVM.AbstRefineConfig False False

ethrunAddress :: EVM.Addr
ethrunAddress = EVM.Addr 0x00a329c0648769a73afac7f9381e08fb43dbea72

initAddr :: EVM.Expr EVM.EAddr
initAddr = EVM.SymAddr "entrypoint"

slotMap :: Store -> Layout
slotMap store =
  M.map (M.map (\(_, slot) -> slot)) store

-- Create a calldata that matches the interface of a certain behaviour
-- or constructor. Use an abstract txdata buffer as the base.
makeCalldata :: Interface -> Calldata
makeCalldata iface@(Interface _ decls) =
  let
    mkArg :: Decl -> CalldataFragment
    mkArg (Decl typ x) = symAbiArg (T.pack x) typ
    makeSig = T.pack $ makeIface iface
    calldatas = fmap mkArg decls
    (cdBuf, _) = combineFragments calldatas (EVM.ConcreteBuf "")
    withSelector = writeSelector cdBuf makeSig
    sizeConstraints
      = (bufLength withSelector EVM..>= cdLen calldatas)
        EVM..&& (bufLength withSelector EVM..< (EVM.Lit (2 ^ (64 :: Integer))))
  in (withSelector, [sizeConstraints])

makeCtrCalldata :: Interface -> Calldata
makeCtrCalldata (Interface _ decls) =
  let
    mkArg :: Decl -> CalldataFragment
    mkArg (Decl typ x) = symAbiArg (T.pack x) typ
    calldatas = fmap mkArg decls
    -- We need to use a concrete buf as a base here because hevm bails when trying to execute with an abstract buf
    -- This is because hevm ends up trying to execute a codecopy with a symbolic size, which is unsupported atm
    -- This is probably unsound, but theres not a lot we can do about it at the moment...
    (cdBuf, props) = combineFragments' calldatas 0 (EVM.ConcreteBuf "")
  in (cdBuf, props)

-- TODO move to HEVM
combineFragments' :: [CalldataFragment] -> EVM.W256 -> EVM.Expr EVM.Buf -> (EVM.Expr EVM.Buf, [EVM.Prop])
combineFragments' fragments start base = go (EVM.Lit start) fragments (base, [])
  where
    go :: EVM.Expr EVM.EWord -> [CalldataFragment] -> (EVM.Expr EVM.Buf, [EVM.Prop]) -> (EVM.Expr EVM.Buf, [EVM.Prop])
    go _ [] acc = acc
    go idx (f:rest) (buf, ps) =
      case f of
        St p w -> go (add idx (EVM.Lit 32)) rest (writeWord idx w buf, p <> ps)
        s -> error $ "unsupported cd fragment: " <> show s


-- * Act translation

translateActBehvs :: CodeMap -> Store -> [Behaviour] -> BS.ByteString -> [(Id, [EVM.Expr EVM.End], Calldata)]
translateActBehvs codemap store behvs bytecode =
  translateBehvs codemap (slotMap store) bytecode behvs

translateActConstr :: CodeMap -> Store -> Contract -> BS.ByteString -> (Id, [EVM.Expr EVM.End], Calldata)
translateActConstr codemap store (Contract ctor _) bytecode = translateConstructor codemap (slotMap store) ctor bytecode

translateConstructor :: CodeMap -> Layout -> Constructor -> BS.ByteString -> (Id, [EVM.Expr EVM.End], Calldata)
translateConstructor codemap layout (Constructor cid iface preconds _ _ upds _) bytecode =
  ("Test", [EVM.Success (snd calldata <> (fmap (toProp layout) $ preconds) <> symAddrCnstr) mempty (EVM.ConcreteBuf bytecode) cmap],
   calldata)
  where
    calldata = makeCtrCalldata iface
    initcontract = EVM.C { EVM.code  = EVM.RuntimeCode (EVM.ConcreteRuntimeCode bytecode)
                         , EVM.storage = EVM.ConcreteStore mempty
                         , EVM.balance = EVM.Lit 0
                         , EVM.nonce = Just 1
                         }
    initmap = M.fromList [(initAddr, initcontract)]
    symAddrCnstr = fmap (\i -> EVM.PNeg (EVM.PEq (EVM.WAddr (EVM.SymAddr $ "freshSymAddr" <> (T.pack $ show i))) (EVM.Lit 0))) [1..nonce-1]
    (cmap, _) = updatesToExpr codemap layout cid initAddr upds (initmap, []) -- TODO remove caller preconditions from the return type if not needed

    nonce :: Integer
    nonce = case M.lookup initAddr cmap of
                 Just (EVM.C _ _ _ n') -> case n' of
                                            Just n -> fromIntegral n
                                            Nothing -> error "Internal error: expecing nonce"
                 Just (EVM.GVar _) -> error "Internal error: unexpected GVar"
                 Nothing -> error "Internal error: init contract not found"


translateBehvs :: CodeMap -> Layout -> BS.ByteString -> [Behaviour] -> [(Id, [EVM.Expr EVM.End], Calldata)]
translateBehvs codemap layout bytecode behvs =
  let groups = (groupBy sameIface behvs) :: [[Behaviour]] in
  fmap (\behvs' -> (behvName behvs', fmap (translateBehv codemap layout bytecode) behvs', behvCalldata behvs')) groups
  where

    behvCalldata (Behaviour _ _ iface _ _ _ _ _:_) = makeCalldata iface
    behvCalldata [] = error "Internal error: behaviour groups cannot be empty"

    -- TODO remove reduntant name in behaviours
    sameIface (Behaviour _ _ iface  _ _ _ _ _) (Behaviour _ _ iface' _ _ _ _ _) =
      makeIface iface == makeIface iface'

    behvName (Behaviour _ _ (Interface name _) _ _ _ _ _:_) = name
    behvName [] = error "Internal error: behaviour groups cannot be empty"

translateBehv :: CodeMap -> Layout -> BS.ByteString -> Behaviour -> EVM.Expr EVM.End
translateBehv codemap layout bytecode (Behaviour _ cid _ preconds caseconds _ upds ret) =
  EVM.Success (fmap (toProp layout) $ preconds <> caseconds) mempty (returnsToExpr layout ret) (rewritesToExpr codemap layout cid upds bytecode)

rewritesToExpr :: CodeMap -> Layout -> Id -> [Rewrite] -> BS.ByteString -> ContractMap
rewritesToExpr codemap layout cid rewrites bytecode = foldl (flip $ rewriteToExpr codemap layout cid initAddr) initmap rewrites
  where
    initcontract = EVM.C { EVM.code  = EVM.RuntimeCode (EVM.ConcreteRuntimeCode bytecode)
                         , EVM.storage = EVM.AbstractStore initAddr
                         , EVM.balance = EVM.Balance (EVM.SymAddr "entrypoint")
                         , EVM.nonce = Just 0
                         }
    initmap = M.fromList [(initAddr, initcontract)]

rewriteToExpr :: CodeMap -> Layout -> Id -> EVM.Expr EVM.EAddr -> Rewrite -> ContractMap -> ContractMap
rewriteToExpr _ _ _ _ (Constant _) cmap = cmap
rewriteToExpr codemap layout cid caddr (Rewrite upd) cmap = fst $ updateToExpr codemap layout cid caddr upd (cmap, [])

updatesToExpr :: CodeMap -> Layout -> Id -> EVM.Expr EVM.EAddr -> [StorageUpdate] -> (ContractMap, [EVM.Prop]) -> (ContractMap, [EVM.Prop])
updatesToExpr codemap layout cid caddr upds initmap = foldl (flip $ updateToExpr codemap layout cid caddr) initmap upds

updateToExpr :: CodeMap -> Layout -> Id -> EVM.Expr EVM.EAddr -> StorageUpdate -> (ContractMap, [EVM.Prop]) -> (ContractMap, [EVM.Prop])
updateToExpr codemap layout cid caddr (Update typ i@(Item _ _ ref) e) (cmap, conds) =
  case typ of
    SInteger -> (M.insert caddr (updateStorage (EVM.SStore offset e') contract) cmap, conds)
    SBoolean -> (M.insert caddr (updateStorage (EVM.SStore offset e') contract) cmap, conds)
    SByteStr -> error "Bytestrings not supported"
    SContract -> let (cmap', preconds) = createContract codemap layout freshAddr cmap e in
      (M.insert caddr (updateNonce (updateStorage (EVM.SStore offset (EVM.WAddr freshAddr)) contract)) cmap', conds <> preconds)
  where
    slot = getSlot layout cid (idFromItem i)
    offset = offsetFromRef layout slot ref

    e' = toExpr layout e
    contract = fromMaybe (error "Internal error: contract not found") $ M.lookup caddr cmap

    updateStorage :: (EVM.Expr EVM.Storage -> EVM.Expr EVM.Storage) -> EVM.Expr EVM.EContract -> EVM.Expr EVM.EContract
    updateStorage updfun c'@(EVM.C _ _ _ _) = c' { EVM.storage = updfun c'.storage }
    updateStorage _ (EVM.GVar _) = error "Internal error: contract cannot be a global variable"

    nonce :: Integer
    nonce = case contract of
      EVM.C _ _ _ (Just n) -> fromIntegral n
      EVM.C _ _ _ _ -> error "Internal error: nonce must be a number"
      EVM.GVar _ -> error "Internal error: contract cannot be a global variable"

    freshAddr = EVM.SymAddr $ "freshSymAddr" <> (T.pack $ show nonce)

    updateNonce :: EVM.Expr EVM.EContract -> EVM.Expr EVM.EContract
    updateNonce c'@(EVM.C _ _ _ (Just n)) = c' { EVM.nonce = Just (n + 1) }
    updateNonce (EVM.C _ _ _ Nothing) = error "Internal error: nonce must be a number"
    updateNonce (EVM.GVar _) = error "Internal error: contract cannot be a global variable"

createContract :: CodeMap -> Layout -> EVM.Expr EVM.EAddr -> ContractMap -> Exp AContract -> (ContractMap, [EVM.Prop])
createContract codemap layout freshAddr cmap (Create _ cid args) =
  case M.lookup cid codemap of
    Just (Contract (Constructor _ iface preconds _ _ upds _) _, _, bytecode) ->
      let contract = EVM.C { EVM.code  = EVM.RuntimeCode (EVM.ConcreteRuntimeCode bytecode)
                           , EVM.storage = EVM.ConcreteStore mempty
                           , EVM.balance = EVM.Lit 0
                           , EVM.nonce = Just 1
                           } in
      let subst = makeSubstMap iface args in
      let preconds' = fmap (toProp layout) $ fmap (substExp subst) preconds in
      let upds' = substUpds subst upds in
      -- trace "Before" $
      -- traceShow preconds $
      -- trace "After" $     
      -- traceShow (fmap (substExp subst) preconds) $
      updatesToExpr codemap layout cid freshAddr upds' (M.insert freshAddr contract cmap, preconds')
    Nothing -> error "Internal error: constructor not found"
createContract _ _ _ _ _ = error "Internal error: constructor call expected"

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



returnsToExpr :: Layout -> Maybe TypedExp -> EVM.Expr EVM.Buf
returnsToExpr _ Nothing = EVM.ConcreteBuf ""
returnsToExpr layout (Just r) = typedExpToBuf layout r

offsetFromRef :: Layout -> Integer -> StorageRef -> EVM.Expr EVM.EWord
offsetFromRef _ slot (SVar _ _ _) = EVM.Lit $ fromIntegral slot
offsetFromRef layout slot (SMapping _ _ ixs) =
  foldl (\slot' i -> EVM.keccak ((typedExpToBuf layout i) <> (wordToBuf slot'))) (EVM.Lit $ fromIntegral slot) ixs
offsetFromRef _ _ (SField _ _ _ _) = error "TODO contracts not supported"

wordToBuf :: EVM.Expr EVM.EWord -> EVM.Expr EVM.Buf
wordToBuf w = EVM.WriteWord (EVM.Lit 0) w (EVM.ConcreteBuf "")

wordToProp :: EVM.Expr EVM.EWord -> EVM.Prop
wordToProp w = EVM.PNeg (EVM.PEq w (EVM.Lit 0))

typedExpToBuf :: Layout -> TypedExp -> EVM.Expr EVM.Buf
typedExpToBuf layout expr =
  case expr of
    TExp styp e -> expToBuf layout styp e

expToBuf :: forall a. Layout -> SType a -> Exp a  -> EVM.Expr EVM.Buf
expToBuf layout styp e =
  case styp of
    SInteger -> EVM.WriteWord (EVM.Lit 0) (toExpr layout e) (EVM.ConcreteBuf "")
    SBoolean -> EVM.WriteWord (EVM.Lit 0) (toExpr layout e) (EVM.ConcreteBuf "")
    SByteStr -> toExpr layout e
    SContract -> error "Internal error: expecting primitive type"

getSlot :: Layout -> Id -> Id -> Integer
getSlot layout cid name =
  case M.lookup cid layout of
    Just m -> case M.lookup name m of
      Just v -> v
      Nothing -> error $ "Internal error: invalid variable name: " <> show name
    Nothing -> error "Internal error: invalid contract name"

refOffset :: Layout -> StorageRef -> EVM.Expr EVM.EWord
refOffset layout (SVar _ cid name) =
  let slot = getSlot layout cid name in
  EVM.Lit $ fromIntegral slot
refOffset layout (SMapping _ ref ixs) =
  let slot = refOffset layout ref in
  foldl (\slot' i -> EVM.keccak ((typedExpToBuf layout i) <> (wordToBuf slot'))) slot ixs
refOffset _ _ = error "TODO"

ethEnvToWord :: EthEnv -> EVM.Expr EVM.EWord
ethEnvToWord Callvalue = EVM.TxValue
ethEnvToWord Caller = EVM.WAddr $ EVM.SymAddr "caller"
ethEnvToWord Origin = EVM.Origin
ethEnvToWord Blocknumber = EVM.BlockNumber
ethEnvToWord Blockhash = EVM.BlockHash $ EVM.Lit 0
ethEnvToWord Chainid = EVM.ChainId
ethEnvToWord Gaslimit = EVM.GasLimit
ethEnvToWord Coinbase = EVM.Coinbase
ethEnvToWord Timestamp = EVM.Timestamp
ethEnvToWord This = error "TODO"
ethEnvToWord Nonce = error "TODO"
ethEnvToWord Calldepth = error "TODO"
ethEnvToWord Difficulty = error "TODO"

ethEnvToBuf :: EthEnv -> EVM.Expr EVM.Buf
ethEnvToBuf _ = error "Internal error: there are no bytestring environment values"


toProp :: Layout -> Exp ABoolean -> EVM.Prop
toProp layout = \case
  (And _ e1 e2) -> pop2 EVM.PAnd e1 e2
  (Or _ e1 e2) -> pop2 EVM.POr e1 e2
  (Impl _ e1 e2) -> pop2 EVM.PImpl e1 e2
  (Neg _ e1) -> EVM.PNeg (toProp layout e1)
  (Syntax.Annotated.LT _ e1 e2) -> op2 EVM.PLT e1 e2
  (LEQ _ e1 e2) -> op2 EVM.PLEq e1 e2
  (GEQ _ e1 e2) -> op2 EVM.PGEq e1 e2
  (Syntax.Annotated.GT _ e1 e2) -> op2 EVM.PGT e1 e2
  (LitBool _ b) -> EVM.PBool b
  (Eq _ SInteger e1 e2) -> op2 EVM.PEq e1 e2
  (Eq _ SBoolean e1 e2) -> op2 EVM.PEq e1 e2
  (Eq _ _ _ _) -> error "unsupported"
  (NEq _ SInteger e1 e2) -> EVM.PNeg $ op2 EVM.PEq e1 e2
  (NEq _ SBoolean e1 e2) -> EVM.PNeg $ op2 EVM.PEq e1 e2
  (NEq _ _ _ _) -> error "unsupported"
  (ITE _ _ _ _) -> error "Internal error: expecting flat expression"
  (Var _ _ _ _) -> error "TODO"
  (TEntry _ _ _) -> error "TODO" -- EVM.SLoad addr idx
  (InRange _ t e) -> toProp layout (inRange t e)
  where
    op2 :: forall a b. (EVM.Expr (ExprType b) -> EVM.Expr (ExprType b) -> a) -> Exp b -> Exp b -> a
    op2 op e1 e2 = op (toExpr layout e1) (toExpr layout e2)

    pop2 :: forall a. (EVM.Prop -> EVM.Prop -> a) -> Exp ABoolean -> Exp ABoolean -> a
    pop2 op e1 e2 = op (toProp layout e1) (toProp layout e2)



toExpr :: forall a. Layout -> Exp a -> EVM.Expr (ExprType a)
toExpr layout = \case
  -- booleans
  (And _ e1 e2) -> op2 EVM.And e1 e2
  (Or _ e1 e2) -> op2 EVM.Or e1 e2
  (Impl _ e1 e2) -> op2 (\x y -> EVM.Or (EVM.Not x) y) e1 e2
  (Neg _ e1) -> EVM.Not (toExpr layout e1)
  (Syntax.Annotated.LT _ e1 e2) -> op2 EVM.LT e1 e2
  (LEQ _ e1 e2) -> op2 EVM.LEq e1 e2
  (GEQ _ e1 e2) -> op2 EVM.GEq e1 e2
  (Syntax.Annotated.GT _ e1 e2) -> op2 EVM.GT e1 e2
  (LitBool _ b) -> EVM.Lit (fromIntegral $ fromEnum $ b)
  -- integers
  (Add _ e1 e2) -> op2 EVM.Add e1 e2
  (Sub _ e1 e2) -> op2 EVM.Sub e1 e2
  (Mul _ e1 e2) -> op2 EVM.Mul e1 e2
  (Div _ e1 e2) -> op2 EVM.Div e1 e2
  (Mod _ e1 e2) -> op2 EVM.Mod e1 e2 -- which mod?
  (Exp _ e1 e2) -> op2 EVM.Exp e1 e2
  (LitInt _ n) -> EVM.Lit (fromIntegral n)
  (IntEnv _ env) -> ethEnvToWord env
  -- bounds
  (IntMin _ n) -> EVM.Lit (fromIntegral $ intmin n)
  (IntMax _ n) -> EVM.Lit (fromIntegral $ intmax n)
  (UIntMin _ n) -> EVM.Lit (fromIntegral $ uintmin n)
  (UIntMax _ n) -> EVM.Lit (fromIntegral $ uintmax n)
  (InRange _ t e) -> toExpr layout (inRange t e)
  -- bytestrings
  (Cat _ _ _) -> error "TODO"
  (Slice _ _ _ _) -> error "TODO"
  -- EVM.CopySlice (toExpr start) (EVM.Lit 0) -- src and dst offset
  -- (EVM.Add (EVM.Sub (toExp end) (toExpr start)) (EVM.Lit 0)) -- size
  -- (toExpr bs) (EVM.ConcreteBuf "") -- src and dst
  (ByStr _ str) -> EVM.ConcreteBuf (B8.pack str)
  (ByLit _ bs) -> EVM.ConcreteBuf bs
  (ByEnv _ env) -> ethEnvToBuf env
  -- contracts
  (Create _ _ _) -> error "TODO"
  -- polymorphic
  (Eq _ SInteger e1 e2) -> op2 EVM.Eq e1 e2
  (Eq _ SBoolean e1 e2) -> op2 EVM.Eq e1 e2
  (Eq _ _ _ _) -> error "unsupported"

  (NEq _ SInteger e1 e2) -> EVM.Not $ op2 EVM.Eq e1 e2
  (NEq _ SBoolean e1 e2) -> EVM.Not $ op2 EVM.Eq e1 e2
  (NEq _ _ _ _) -> error "unsupported"

  (ITE _ _ _ _) -> error "Internal error: expecting flat expression"

  (Var _ SInteger typ x) ->  -- TODO other types
    fromCalldataFramgment $ symAbiArg (T.pack x) typ

  (TEntry _ _ (Item SInteger _ ref)) ->
    let slot = refOffset layout ref in
    EVM.SLoad slot (EVM.AbstractStore initAddr) -- TODO fix address

  e ->  error $ "TODO: " <> show e

  where
    op2 :: forall b c. (EVM.Expr (ExprType c) -> EVM.Expr (ExprType c) -> b) -> Exp c -> Exp c -> b
    op2 op e1 e2 = op (toExpr layout e1) (toExpr layout e2)

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
checkEquiv :: SolverGroup -> VeriOpts -> [EVM.Expr EVM.End] -> [EVM.Expr EVM.End] -> IO [EquivResult]
checkEquiv solvers opts l1 l2 =
  fmap toEquivRes <$> equivalenceCheck' solvers l1 l2 opts
  where
    toEquivRes :: SymExec.EquivResult -> EquivResult
    toEquivRes (Cex cex) = Cex ("\x1b[1mThe following input results in different behaviours\x1b[m", cex)
    toEquivRes (Qed a) = Qed a
    toEquivRes (Timeout b) = Timeout b


checkConstructors :: SolverGroup -> VeriOpts -> ByteString -> ByteString -> Store -> Contract -> CodeMap -> IO ()
checkConstructors solvers opts initcode runtimecode store contract codemap = do
  let (_, actbehvs, calldata) = translateActConstr codemap store contract runtimecode
  initVM <- stToIO $ abstractVM calldata initcode Nothing True
  expr <- interpret (Fetch.oracle solvers Nothing) Nothing 1 StackBased initVM runExpr
  let simpl = if True then (simplify expr) else expr
  -- traceM (T.unpack $ Format.formatExpr simpl)
  let solbehvs = removeFails $ flattenExpr simpl
  -- mapM_ (traceM . T.unpack . Format.formatExpr) solbehvs
  -- mapM_ (traceM . T.unpack . Format.formatExpr) actbehvs
  putStrLn "\x1b[1mChecking if constructor results are equivalent.\x1b[m"
  checkResult =<< checkEquiv solvers opts solbehvs actbehvs
  putStrLn "\x1b[1mChecking if constructor input spaces are the same.\x1b[m"
  checkResult =<< checkInputSpaces solvers opts solbehvs actbehvs
  where
    removeFails branches = filter isSuccess $ branches


checkBehaviours :: SolverGroup -> VeriOpts -> ByteString -> Store -> Contract -> CodeMap -> IO ()
checkBehaviours solvers opts bytecode store (Contract _ behvs) codemap = do
  let actbehvs = translateActBehvs codemap store behvs bytecode
  flip mapM_ actbehvs $ \(name,behvs',calldata) -> do
    solbehvs <- removeFails <$> getBranches solvers bytecode calldata
    putStrLn $ "\x1b[1mChecking behavior \x1b[4m" <> name <> "\x1b[m of Act\x1b[m"
    -- equivalence check
    putStrLn "\x1b[1mChecking if behaviour is matched by EVM\x1b[m"
    checkResult =<< checkEquiv solvers opts solbehvs behvs'
    -- input space exhaustiveness check
    putStrLn "\x1b[1mChecking if the input spaces are the same\x1b[m"
    checkResult =<< checkInputSpaces solvers opts solbehvs behvs'
    where
      removeFails branches = filter isSuccess $ branches

-- | Find the input space of an expr list
inputSpace :: [EVM.Expr EVM.End] -> [EVM.Prop]
inputSpace exprs = map aux exprs
  where
    aux :: EVM.Expr EVM.End -> EVM.Prop
    aux (EVM.Success c _ _ _) = EVM.pand c
    aux _ = error "List should only contain success behaviours"

-- | Check whether two lists of behaviours cover exactly the same input space
checkInputSpaces :: SolverGroup -> VeriOpts -> [EVM.Expr EVM.End] -> [EVM.Expr EVM.End] -> IO [EquivResult]
checkInputSpaces solvers opts l1 l2 = do
  let p1 = inputSpace l1
  let p2 = inputSpace l2
  let queries = fmap (assertProps abstRefineDefault) [ [ EVM.PNeg (EVM.por p1), EVM.por p2 ]
                                                     , [ EVM.por p1, EVM.PNeg (EVM.por p2) ] ]

  when opts.debug $ forM_ (zip [(1 :: Int)..] queries) $ \(idx, q) -> do
    TL.writeFile
      ("input-query-" <> show idx <> ".smt2")
      (formatSMT2 q <> "\n\n(check-sat)")

  results <- mapConcurrently (checkSat solvers) queries
  let results' = case results of
                   [r1, r2] -> [ toVRes "\x1b[1mThe following inputs are accepted by Act but not EVM\x1b[m" r1
                               , toVRes "\x1b[1mThe following inputs are accepted by EVM but not Act\x1b[m" r2 ]
                   _ -> error "Internal error: impossible"

  case all isQed results' of
    True -> pure [Qed ()]
    False -> pure $ filter (/= Qed ()) results'


-- | Checks whether all successful EVM behaviors are withing the
-- interfaces specified by Act
checkAbi :: SolverGroup -> VeriOpts -> Contract -> BS.ByteString -> IO ()
checkAbi solver opts contract bytecode = do
  putStrLn "\x1b[1mChecking if the ABI of the contract matches the specification\x1b[m"
  let txdata = EVM.AbstractBuf "txdata"
  let selectorProps = assertSelector txdata <$> nubOrd (actSigs contract)
  evmBehvs <- getBranches solver bytecode (txdata, [])
  let queries =  fmap (assertProps abstRefineDefault) $ filter (/= []) $ fmap (checkBehv selectorProps) evmBehvs

  when opts.debug $ forM_ (zip [(1 :: Int)..] queries) $ \(idx, q) -> do
    TL.writeFile
      ("abi-query-" <> show idx <> ".smt2")
      (formatSMT2 q <> "\n\n(check-sat)")

  checkResult =<< fmap (toVRes msg) <$> mapConcurrently (checkSat solver) queries

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

checkContracts :: SolverGroup -> VeriOpts -> Store -> M.Map Id (Contract, BS.ByteString, BS.ByteString) -> IO ()
checkContracts solvers opts store codemap =
  mapM_ (\(_, (contract, initcode, bytecode)) -> do
            putStrLn $ "\x1b[1mChecking contract \x1b[4m" <> nameOfContract contract <> "\x1b[m"
            -- Constructor check
            checkConstructors solvers opts initcode bytecode store contract codemap
            -- Behavours check
            checkBehaviours solvers opts bytecode store contract codemap
            -- ABI exhaustiveness sheck
            checkAbi solvers opts contract bytecode
        ) (M.toList codemap)



-- | decompiles the given EVM bytecode into a list of Expr branches
getBranches :: SolverGroup -> BS.ByteString -> Calldata -> IO [EVM.Expr EVM.End]
getBranches solvers bs calldata = do
      let bytecode = if BS.null bs then BS.pack [0] else bs
      prestate <- stToIO $ abstractVM calldata bytecode Nothing False
      expr <- interpret (Fetch.oracle solvers Nothing) Nothing 1 StackBased prestate runExpr
      let simpl = if True then (simplify expr) else expr
      let nodes = flattenExpr simpl

      when (any isPartial nodes) $ do
        putStrLn ""
        putStrLn "WARNING: hevm was only able to partially explore the given contract due to the following issues:"
        putStrLn ""
        TIO.putStrLn . T.unlines . fmap (Format.indent 2 . ("- " <>)) . fmap Format.formatPartial . nubOrd $ (getPartials nodes)

      pure nodes

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


checkResult :: [EquivResult] -> IO ()
checkResult res =
  case any isCex res of
    False -> do
      putStrLn "\x1b[42mNo discrepancies found\x1b[m"
      when (any isTimeout res) $ do
        putStrLn "But timeout(s) occurred"
        exitFailure
    True -> do
      let cexs = mapMaybe getCex res
      TIO.putStrLn . T.unlines $
        [ "\x1b[41mNot equivalent.\x1b[m"
        , "" , "-----", ""
        ] <> (intersperse (T.unlines [ "", "-----" ]) $ fmap (\(msg, cex) -> msg <> "\n" <> formatCex (EVM.AbstractBuf "txdata") cex) cexs)
      exitFailure
