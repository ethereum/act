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

module Expr where

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

import qualified EVM.Types as Types
import EVM.Concrete (createAddress)
import EVM.Expr hiding (op2, inRange)
import EVM.SymExec
import EVM.SMT (assertProps, formatSMT2)
import EVM.Solvers

type family ExprType a where
  ExprType 'AInteger  = Types.EWord
  ExprType 'ABoolean  = Types.EWord
  ExprType 'AByteStr  = Types.Buf
  ExprType 'AContract = Types.EWord -- adress?

type Layout = M.Map Id (M.Map Id (Types.Addr, Integer))

ethrunAddress :: Types.Addr
ethrunAddress = Types.Addr 0x00a329c0648769a73afac7f9381e08fb43dbea72

slotMap :: Store -> Layout
slotMap store =
  let addr = createAddress ethrunAddress 1 in -- for now all contracts have the same address
  M.map (M.map (\(_, slot) -> (addr, slot))) store

-- TODO move this to HEVM
type Calldata = (Types.Expr Types.Buf, [Types.Prop])

-- Create a calldata that matches the interface of a certain behaviour
-- or constructor. Use an abstract txdata buffer as the base.
makeCalldata :: Interface -> Calldata
makeCalldata iface@(Interface _ decls) =
  let
    mkArg :: Decl -> CalldataFragment
    mkArg (Decl typ x)  = symAbiArg (T.pack x) typ
    makeSig = T.pack $ makeIface iface
    calldatas = fmap mkArg decls
    (cdBuf, props) = combineFragments calldatas (Types.ConcreteBuf "")
    withSelector = writeSelector cdBuf makeSig
    sizeConstraints
      = (bufLength withSelector Types..>= cdLen calldatas)
        Types..&& (bufLength withSelector Types..< (Types.Lit (2 ^ (64 :: Integer))))
  in (withSelector, sizeConstraints : props)

makeCtrCalldata :: Interface -> Calldata
makeCtrCalldata (Interface _ decls) =
  let
    mkArg :: Decl -> CalldataFragment
    mkArg (Decl typ x)  = symAbiArg (T.pack x) typ
    calldatas = fmap mkArg decls
    (cdBuf, props) = combineFragments' calldatas 0 (Types.AbstractBuf "txdata")
  in (cdBuf, props)

-- TODO move to HEVM
combineFragments' :: [CalldataFragment] -> Types.W256 -> Types.Expr Types.Buf -> (Types.Expr Types.Buf, [Types.Prop])
combineFragments' fragments start base = go (Types.Lit start) fragments (base, [])
  where
    go :: Types.Expr Types.EWord -> [CalldataFragment] -> (Types.Expr Types.Buf, [Types.Prop]) -> (Types.Expr Types.Buf, [Types.Prop])
    go _ [] acc = acc
    go idx (f:rest) (buf, ps) =
      case f of
        St p w -> go (add idx (Types.Lit 32)) rest (writeWord idx w buf, p <> ps)
        s -> error $ "unsupported cd fragment: " <> show s


translateAct :: Act -> [([Types.Expr Types.End], Calldata)]
translateAct (Act store contracts) =
  let slots = slotMap store in
  concatMap (\(Contract _ behvs) -> translateBehvs slots behvs) contracts

translateConstructor :: Layout -> Constructor -> ([Types.Expr Types.End], Calldata)
translateConstructor layout (Constructor cid iface preconds _ _ upds _) =
  ([Types.Success (snd calldata <> (fmap (toProp layout) $ preconds)) (returnsToExpr layout Nothing) (updatesToExpr layout cid upds)],
   calldata)

  where calldata = makeCtrCalldata iface

translateBehvs :: Layout -> [Behaviour] -> [([Types.Expr Types.End], Calldata)]
translateBehvs layout behvs =
  let groups = (groupBy sameIface behvs) :: [[Behaviour]] in
  fmap (\behvs' -> (fmap (translateBehv layout) behvs', behvCalldata behvs')) groups
  where
    behvCalldata (Behaviour _ _ iface _ _ _ _ _:_) = makeCalldata iface
    behvCalldata [] = error "Internal error: behaviour groups cannot be empty"

    -- TODO remove reduntant name in behaviours
    sameIface (Behaviour _ _ iface  _ _ _ _ _) (Behaviour _ _ iface' _ _ _ _ _) =
      makeIface iface == makeIface iface'


translateBehv :: Layout -> Behaviour -> Types.Expr Types.End
translateBehv layout (Behaviour _ cid _ preconds caseconds _ upds ret) =
  Types.Success (fmap (toProp layout) $ preconds <> caseconds) (returnsToExpr layout ret) (rewritesToExpr layout cid upds)

rewritesToExpr :: Layout -> Id -> [Rewrite] -> Types.Expr Types.Storage
rewritesToExpr layout cid rewrites = foldl (flip $ rewriteToExpr layout cid) Types.AbstractStore rewrites

rewriteToExpr :: Layout -> Id -> Rewrite -> Types.Expr Types.Storage -> Types.Expr Types.Storage
rewriteToExpr _ _ (Constant _) state = state
rewriteToExpr layout cid (Rewrite upd) state = updateToExpr layout cid upd state

updatesToExpr :: Layout -> Id -> [StorageUpdate] -> Types.Expr Types.Storage
updatesToExpr layout cid upds = foldl (flip $ updateToExpr layout cid) Types.AbstractStore upds

updateToExpr :: Layout -> Id -> StorageUpdate -> Types.Expr Types.Storage -> Types.Expr Types.Storage
updateToExpr layout cid (Update typ i@(Item _ _ ref) e) state =
  case typ of
    SInteger -> Types.SStore (Types.Lit $ fromIntegral addr) offset e' state
    SBoolean -> Types.SStore (Types.Lit $ fromIntegral addr) offset e' state
    SByteStr -> error "Bytestrings not supported"
    SContract -> error "Contracts not supported"
  where
    (addr, slot) = getSlot layout cid (idFromItem i)
    offset = offsetFromRef layout slot ref
    e' = toExpr layout e

returnsToExpr :: Layout -> Maybe TypedExp -> Types.Expr Types.Buf
returnsToExpr _ Nothing = Types.ConcreteBuf ""
returnsToExpr layout (Just r) = typedExpToBuf layout r

offsetFromRef :: Layout -> Integer -> StorageRef -> Types.Expr Types.EWord
offsetFromRef _ slot (SVar _ _ _) = Types.Lit $ fromIntegral slot
offsetFromRef layout slot (SMapping _ _ ixs) =
  foldl (\slot' i -> Types.keccak ((typedExpToBuf layout i) <> (wordToBuf slot'))) (Types.Lit $ fromIntegral slot) ixs
offsetFromRef _ _ (SField _ _ _ _) = error "TODO contracts not supported"

wordToBuf :: Types.Expr Types.EWord -> Types.Expr Types.Buf
wordToBuf w = Types.WriteWord (Types.Lit 0) w (Types.ConcreteBuf "")

wordToProp :: Types.Expr Types.EWord -> Types.Prop
wordToProp w = Types.PNeg (Types.PEq w (Types.Lit 0))

typedExpToBuf :: Layout -> TypedExp -> Types.Expr Types.Buf
typedExpToBuf layout expr =
  case expr of
    TExp styp e -> expToBuf layout styp e

expToBuf :: forall a. Layout -> SType a -> Exp a  -> Types.Expr Types.Buf
expToBuf layout styp e =
  case styp of
    SInteger -> Types.WriteWord (Types.Lit 0) (toExpr layout e) (Types.ConcreteBuf "")
    SBoolean -> Types.WriteWord (Types.Lit 0) (toExpr layout e) (Types.ConcreteBuf "")
    SByteStr -> toExpr layout e
    SContract -> error "Internal error: expecting primitive type"

getSlot :: Layout -> Id -> Id -> (Types.Addr, Integer)
getSlot layout cid name =
  case M.lookup cid layout of
    Just m -> case M.lookup name m of
      Just v -> v
      Nothing -> error $ "Internal error: invalid variable name: " <> show name
    Nothing -> error "Internal error: invalid contract name"

refOffset :: Layout -> StorageRef -> (Types.Addr, Types.Expr Types.EWord)
refOffset layout (SVar _ cid name) =
  let (addr, slot) = getSlot layout cid name in
  (addr, Types.Lit $ fromIntegral slot)
refOffset layout (SMapping _ ref ixs) =
  let (addr, slot) = refOffset layout ref in
  (addr,
   foldl (\slot' i -> Types.keccak ((typedExpToBuf layout i) <> (wordToBuf slot'))) slot ixs)

refOffset _ _ = error "TODO"

ethEnvToWord :: EthEnv -> Types.Expr Types.EWord
ethEnvToWord Callvalue = Types.CallValue 0
ethEnvToWord Caller = Types.Caller 0
ethEnvToWord Origin = Types.Origin
ethEnvToWord Blocknumber = Types.BlockNumber
ethEnvToWord Blockhash = error "TODO" -- Types.BlockHash ??  missing EWord!
ethEnvToWord Chainid = Types.ChainId
ethEnvToWord Gaslimit = Types.GasLimit
ethEnvToWord Coinbase = Types.Coinbase
ethEnvToWord Timestamp = Types.Timestamp
ethEnvToWord This = error "TODO"
ethEnvToWord Nonce = error "TODO"
ethEnvToWord Calldepth = error "TODO"
ethEnvToWord Difficulty = error "TODO"

ethEnvToBuf :: EthEnv -> Types.Expr Types.Buf
ethEnvToBuf _ = error "Internal error: there are no bytestring environment values"


toProp :: Layout -> Exp ABoolean -> Types.Prop
toProp layout = \case
  (And _ e1 e2) -> pop2 Types.PAnd e1 e2
  (Or _ e1 e2) -> pop2 Types.POr e1 e2
  (Impl _ e1 e2) -> pop2 Types.PImpl e1 e2
  (Neg _ e1) -> Types.PNeg (toProp layout e1)
  (Syntax.Annotated.LT _ e1 e2) -> op2 Types.PLT e1 e2
  (LEQ _ e1 e2) -> op2 Types.PLEq e1 e2
  (GEQ _ e1 e2) -> op2 Types.PGEq e1 e2
  (Syntax.Annotated.GT _ e1 e2) -> op2 Types.PGT e1 e2
  (LitBool _ b) -> Types.PBool b
  (Eq _ SInteger e1 e2) -> op2 Types.PEq e1 e2
  (Eq _ SBoolean e1 e2) -> op2 Types.PEq e1 e2
  (Eq _ _ _ _) -> error "unsupported"
  (NEq _ SInteger e1 e2) -> Types.PNeg $ op2 Types.PEq e1 e2
  (NEq _ SBoolean e1 e2) -> Types.PNeg $ op2 Types.PEq e1 e2
  (NEq _ _ _ _) -> error "unsupported"
  (ITE _ _ _ _) -> error "Internal error: expecting flat expression"
  (Var _ _ _) -> error "TODO" -- (Types.Var (T.pack x)) -- vars can only be words? TODO other types
  (TEntry _ _ _) -> error "TODO" -- Types.SLoad addr idx
  (InRange _ t e) -> toProp layout (inRange t e)
  where
    op2 :: forall a b. (Types.Expr (ExprType b) -> Types.Expr (ExprType b) -> a) -> Exp b -> Exp b -> a
    op2 op e1 e2 = op (toExpr layout e1) (toExpr layout e2)

    pop2 :: forall a. (Types.Prop -> Types.Prop -> a) -> Exp ABoolean -> Exp ABoolean -> a
    pop2 op e1 e2 = op (toProp layout e1) (toProp layout e2)



toExpr :: forall a. Layout -> Exp a -> Types.Expr (ExprType a)
toExpr layout = \case
  -- booleans
  (And _ e1 e2) -> op2 Types.And e1 e2
  (Or _ e1 e2) -> op2 Types.Or e1 e2
  (Impl _ e1 e2) -> op2 (\x y -> Types.Or (Types.Not x) y) e1 e2
  (Neg _ e1) -> Types.Not (toExpr layout e1)
  (Syntax.Annotated.LT _ e1 e2) -> op2 Types.LT e1 e2
  (LEQ _ e1 e2) -> op2 Types.LEq e1 e2
  (GEQ _ e1 e2) -> op2 Types.GEq e1 e2
  (Syntax.Annotated.GT _ e1 e2) -> op2 Types.GT e1 e2
  (LitBool _ b) -> Types.Lit (fromIntegral $ fromEnum $ b)
  -- integers
  (Add _ e1 e2) -> op2 Types.Add e1 e2
  (Sub _ e1 e2) -> op2 Types.Sub e1 e2
  (Mul _ e1 e2) -> op2 Types.Mul e1 e2
  (Div _ e1 e2) -> op2 Types.Div e1 e2
  (Mod _ e1 e2) -> op2 Types.Mod e1 e2 -- which mod?
  (Exp _ e1 e2) -> op2 Types.Exp e1 e2
  (LitInt _ n) -> Types.Lit (fromIntegral n)
  (IntEnv _ env) -> ethEnvToWord env
  -- bounds
  (IntMin _ n) -> Types.Lit (fromIntegral $ intmin n)
  (IntMax _ n) -> Types.Lit (fromIntegral $ intmax n)
  (UIntMin _ n) -> Types.Lit (fromIntegral $ uintmin n)
  (UIntMax _ n) -> Types.Lit (fromIntegral $ uintmax n)
  (InRange _ t e) -> toExpr layout (inRange t e)
  -- bytestrings
  (Cat _ _ _) -> error "TODO"
  (Slice _ _ _ _) -> error "TODO"
  -- Types.CopySlice (toExpr start) (Types.Lit 0) -- src and dst offset
  -- (Types.Add (Types.Sub (toExp end) (toExpr start)) (Types.Lit 0)) -- size
  -- (toExpr bs) (Types.ConcreteBuf "") -- src and dst
  (ByStr _ str) -> Types.ConcreteBuf (B8.pack str)
  (ByLit _ bs) -> Types.ConcreteBuf bs
  (ByEnv _ env) -> ethEnvToBuf env
  -- contracts
  (Create _ _ _) -> error "TODO"
  -- polymorphic
  (Eq _ SInteger e1 e2) -> op2 Types.Eq e1 e2
  (Eq _ SBoolean e1 e2) -> op2 Types.Eq e1 e2
  (Eq _ _ _ _) -> error "unsupported"

  (NEq _ SInteger e1 e2) -> Types.Not $ op2 Types.Eq e1 e2
  (NEq _ SBoolean e1 e2) -> Types.Not $ op2 Types.Eq e1 e2
  (NEq _ _ _ _) -> error "unsupported"

  (ITE _ _ _ _) -> error "Internal error: expecting flat expression"

  (Var _ SInteger x) -> (Types.Var (T.pack x)) -- vars can only be words? TODO other types

  (TEntry _ _ (Item SInteger _ ref)) ->
    let (addr, slot) = refOffset layout ref in
    Types.SLoad (litAddr addr) slot Types.AbstractStore
  e ->  error $ "TODO: " <> show e

  where
    op2 :: forall b c. (Types.Expr (ExprType c) -> Types.Expr (ExprType c) -> b) -> Exp c -> Exp c -> b
    op2 op e1 e2 = op (toExpr layout e1) (toExpr layout e2)


-- | Find the input space of an expr list
inputSpace :: [Types.Expr Types.End] -> [Types.Prop]
inputSpace exprs = map aux exprs
  where
    aux :: Types.Expr Types.End -> Types.Prop
    aux (Types.Success c _ _) = Types.pand c
    aux _ = error "List should only contain success behaviours"

-- | Check whether two lists of behaviours cover exactly the same input space
checkInputSpaces :: SolverGroup -> VeriOpts -> [Types.Expr Types.End] -> [Types.Expr Types.End] -> IO [EquivResult]
checkInputSpaces solvers _ l1 l2 = do
  let p1 = inputSpace l1
  let p2 = inputSpace l2
  let queries = fmap assertProps [ [ Types.PNeg (Types.por p1), Types.por p2 ]
                               , [ Types.por p1, Types.PNeg (Types.por p2) ] ]

  when True $ forM_ (zip [(1 :: Int)..] queries) $ \(idx, q) -> do
    TL.writeFile
      ("query-" <> show idx <> ".smt2")
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
