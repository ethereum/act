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


module HEVM where

import qualified Data.Map as M
import Data.List
import qualified Data.Text as T
import qualified Data.Text.Lazy.IO as TL
import qualified Data.ByteString.Char8 as B8 (pack)
import Control.Concurrent.Async
import Control.Monad
import Data.DoubleWord

import Syntax.Annotated
import Syntax.Untyped (makeIface)
import Syntax

import qualified EVM.Types as EVM
import EVM.Concrete (createAddress)
import EVM.Expr hiding (op2, inRange)
import EVM.SymExec
import EVM.SMT (assertProps, formatSMT2)
import EVM.Solvers

type family ExprType a where
  ExprType 'AInteger  = EVM.EWord
  ExprType 'ABoolean  = EVM.EWord
  ExprType 'AByteStr  = EVM.Buf
  ExprType 'AContract = EVM.EWord -- address?

type Layout = M.Map Id (M.Map Id (EVM.Addr, Integer))

ethrunAddress :: EVM.Addr
ethrunAddress = EVM.Addr 0x00a329c0648769a73afac7f9381e08fb43dbea72

slotMap :: Store -> Layout
slotMap store =
  let addr = createAddress ethrunAddress 1 in -- for now all contracts have the same address
  M.map (M.map (\(_, slot) -> (addr, slot))) store

-- TODO move this to HEVM
type Calldata = (EVM.Expr EVM.Buf, [EVM.Prop])

-- Create a calldata that matches the interface of a certain behaviour
-- or constructor. Use an abstract txdata buffer as the base.
makeCalldata :: Interface -> Calldata
makeCalldata iface@(Interface _ decls) =
  let
    mkArg :: Decl -> CalldataFragment
    mkArg (Decl typ x)  = symAbiArg (T.pack x) typ
    makeSig = T.pack $ makeIface iface
    calldatas = fmap mkArg decls
    (cdBuf, props) = combineFragments calldatas (EVM.ConcreteBuf "")
    withSelector = writeSelector cdBuf makeSig
    sizeConstraints
      = (bufLength withSelector EVM..>= cdLen calldatas)
        EVM..&& (bufLength withSelector EVM..< (EVM.Lit (2 ^ (64 :: Integer))))
  in (withSelector, sizeConstraints : props)

makeCtrCalldata :: Interface -> Calldata
makeCtrCalldata (Interface _ decls) =
  let
    mkArg :: Decl -> CalldataFragment
    mkArg (Decl typ x)  = symAbiArg (T.pack x) typ
    calldatas = fmap mkArg decls
    (cdBuf, props) = combineFragments' calldatas 0 (EVM.AbstractBuf "txdata")
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


translateAct :: Act -> [([EVM.Expr EVM.End], Calldata)]
translateAct (Act store contracts) =
  let slots = slotMap store in
  concatMap (\(Contract _ behvs) -> translateBehvs slots behvs) contracts

translateConstructor :: Layout -> Constructor -> ([EVM.Expr EVM.End], Calldata)
translateConstructor layout (Constructor cid iface preconds _ _ upds _) =
  ([EVM.Success (snd calldata <> (fmap (toProp layout) $ preconds)) mempty (returnsToExpr layout Nothing) (updatesToExpr layout cid upds)],
   calldata)

  where calldata = makeCtrCalldata iface

translateBehvs :: Layout -> [Behaviour] -> [([EVM.Expr EVM.End], Calldata)]
translateBehvs layout behvs =
  let groups = (groupBy sameIface behvs) :: [[Behaviour]] in
  fmap (\behvs' -> (fmap (translateBehv layout) behvs', behvCalldata behvs')) groups
  where
    behvCalldata (Behaviour _ _ iface _ _ _ _ _:_) = makeCalldata iface
    behvCalldata [] = error "Internal error: behaviour groups cannot be empty"

    -- TODO remove reduntant name in behaviours
    sameIface (Behaviour _ _ iface  _ _ _ _ _) (Behaviour _ _ iface' _ _ _ _ _) =
      makeIface iface == makeIface iface'


translateBehv :: Layout -> Behaviour -> EVM.Expr EVM.End
translateBehv layout (Behaviour _ cid _ preconds caseconds _ upds ret) =
  EVM.Success (fmap (toProp layout) $ preconds <> caseconds) mempty (returnsToExpr layout ret) (rewritesToExpr layout cid upds)

rewritesToExpr :: Layout -> Id -> [Rewrite] -> EVM.Expr EVM.Storage
rewritesToExpr layout cid rewrites = foldl (flip $ rewriteToExpr layout cid) EVM.AbstractStore rewrites

rewriteToExpr :: Layout -> Id -> Rewrite -> EVM.Expr EVM.Storage -> EVM.Expr EVM.Storage
rewriteToExpr _ _ (Constant _) state = state
rewriteToExpr layout cid (Rewrite upd) state = updateToExpr layout cid upd state

updatesToExpr :: Layout -> Id -> [StorageUpdate] -> EVM.Expr EVM.Storage
updatesToExpr layout cid upds = foldl (flip $ updateToExpr layout cid) EVM.AbstractStore upds

updateToExpr :: Layout -> Id -> StorageUpdate -> EVM.Expr EVM.Storage -> EVM.Expr EVM.Storage
updateToExpr layout cid (Update typ i@(Item _ _ ref) e) state =
  case typ of
    SInteger -> EVM.SStore (EVM.Lit $ fromIntegral addr) offset e' state
    SBoolean -> EVM.SStore (EVM.Lit $ fromIntegral addr) offset e' state
    SByteStr -> error "Bytestrings not supported"
    SContract -> error "Contracts not supported"
  where
    (addr, slot) = getSlot layout cid (idFromItem i)
    offset = offsetFromRef layout slot ref
    e' = toExpr layout e

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

getSlot :: Layout -> Id -> Id -> (EVM.Addr, Integer)
getSlot layout cid name =
  case M.lookup cid layout of
    Just m -> case M.lookup name m of
      Just v -> v
      Nothing -> error $ "Internal error: invalid variable name: " <> show name
    Nothing -> error "Internal error: invalid contract name"

refOffset :: Layout -> StorageRef -> (EVM.Addr, EVM.Expr EVM.EWord)
refOffset layout (SVar _ cid name) =
  let (addr, slot) = getSlot layout cid name in
  (addr, EVM.Lit $ fromIntegral slot)
refOffset layout (SMapping _ ref ixs) =
  let (addr, slot) = refOffset layout ref in
  (addr,
   foldl (\slot' i -> EVM.keccak ((typedExpToBuf layout i) <> (wordToBuf slot'))) slot ixs)

refOffset _ _ = error "TODO"

ethEnvToWord :: EthEnv -> EVM.Expr EVM.EWord
ethEnvToWord Callvalue = EVM.CallValue 0
ethEnvToWord Caller = EVM.Caller 0
ethEnvToWord Origin = EVM.Origin
ethEnvToWord Blocknumber = EVM.BlockNumber
ethEnvToWord Blockhash = error "TODO" -- EVM.BlockHash ??
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
  (Var _ _ _) -> error "TODO" -- (EVM.Var (T.pack x)) -- vars can only be words? TODO other types
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

  (Var _ SInteger x) -> (EVM.Var (T.pack x)) -- vars can only be words? TODO other types

  (TEntry _ _ (Item SInteger _ ref)) ->
    let (addr, slot) = refOffset layout ref in
    EVM.SLoad (litAddr addr) slot EVM.AbstractStore
  e ->  error $ "TODO: " <> show e

  where
    op2 :: forall b c. (EVM.Expr (ExprType c) -> EVM.Expr (ExprType c) -> b) -> Exp c -> Exp c -> b
    op2 op e1 e2 = op (toExpr layout e1) (toExpr layout e2)


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
  let queries = fmap assertProps [ [ EVM.PNeg (EVM.por p1), EVM.por p2 ]
                               , [ EVM.por p1, EVM.PNeg (EVM.por p2) ] ]

  when opts.debug $ forM_ (zip [(1 :: Int)..] queries) $ \(idx, q) -> do
    TL.writeFile
      ("input-query-" <> show idx <> ".smt2")
      (formatSMT2 q <> "\n\n(check-sat)")

  results <- fmap toVRes <$> mapConcurrently (checkSat solvers) queries
  case all isQed results of
    True -> pure [Qed ()]
    False -> pure $ filter (/= Qed ()) results

    where
      toVRes :: CheckSatResult -> EquivResult
      toVRes res = case res of
        Sat cex -> Cex cex
        EVM.Solvers.Unknown -> Timeout ()
        Unsat -> Qed ()
        Error e -> error $ "Internal Error: solver responded with error: " <> show e


-- TODO this is also defined in hevm-cli
getCex :: ProofResult a b c -> Maybe b
getCex (Cex c) = Just c
getCex _ = Nothing


inRange :: AbiType -> Exp AInteger -> Exp ABoolean
-- if the type has the type of machine word then check per operation
inRange (AbiUIntType 256) e = checkOp e
inRange (AbiIntType 256) _ = error "TODO signed integers"
-- otherwise insert range bounds
inRange t e = bound t e


checkOp :: Exp AInteger -> Exp ABoolean
checkOp (LitInt _ i) = LitBool nowhere $ i <= (fromIntegral (maxBound :: Word256))
checkOp (Var _ _ _)  = LitBool nowhere True
checkOp (TEntry _ _ _)  = LitBool nowhere True
checkOp e@(Add _ e1 _) = LEQ nowhere e1 e -- check for addition overflow
checkOp e@(Sub _ e1 _) = LEQ nowhere e e1
checkOp e@(Mul _ e1 _) = LEQ nowhere e e1
checkOp (Div _ _ _) = LitBool nowhere True
checkOp (Mod _ _ _) = LitBool nowhere True
checkOp (Exp _ _ _) = error "TODO check for exponentiation overflow"
checkOp (IntMin _ _)  = error "Internal error: invalid in range expression"
checkOp (IntMax _ _)  = error "Internal error: invalid in range expression"
checkOp (UIntMin _ _) = error "Internal error: invalid in range expression"
checkOp (UIntMax _ _) = error "Internal error: invalid in range expression"
checkOp (ITE _ _ _ _) = error "Internal error: invalid in range expression"
checkOp (IntEnv _ _) = error "Internal error: invalid in range expression"
