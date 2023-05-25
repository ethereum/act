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
import qualified Data.Text as T
import qualified Data.ByteString.Char8 as B8 (pack)

import Syntax.Annotated
import Syntax

import qualified EVM.Types as Types
import EVM.Concrete (createAddress)
import EVM.Expr hiding (op2)

-- decompile :: Contract -> ByteString -> IO (Map Interface [Expr End])

type family ExprType a where
  ExprType 'AInteger  = Types.EWord
  ExprType 'ABoolean  = Types.EWord
  ExprType 'AByteStr  = Types.Buf
  ExprType 'AContract = Types.EWord -- adress?


type Layout = M.Map Id (M.Map Id (Types.Addr, Integer))
  
slotMap :: [Contract] -> Layout
slotMap contracts =
  foldl (\layout (Contract Constructor{..} _) ->
            let addr = createAddress (Types.Addr 0) 0 in -- for now all contracts have the same address
            let varmap = addVars addr _initialStorage in
              M.insert _cname varmap layout
        ) M.empty contracts
  where
    addVars addr upds =
      foldl (\layout (upd, i) -> M.insert (idFromUpdate upd) (addr, i) layout) M.empty $ zip upds [0..]


translateAct :: Act -> [Types.Expr Types.End]
translateAct (Act _ contracts) =
  let slots = slotMap contracts in
  concatMap (\(Contract _ behvs) -> map (translateBehv slots) behvs) contracts

  
translateBehv :: Layout -> Behaviour -> Types.Expr Types.End
translateBehv layout (Behaviour _ cid _ preconds caseconds _ upds ret) =  
  Types.Success (fmap toProp $ preconds <> caseconds) (returnsToExpr ret) (rewritesToExpr layout cid upds)

rewritesToExpr :: Layout -> Id -> [Rewrite] -> Types.Expr Types.Storage
rewritesToExpr layout cid rewrites = foldl (flip $ rewriteToExpr layout cid) Types.AbstractStore rewrites

rewriteToExpr :: Layout -> Id -> Rewrite -> Types.Expr Types.Storage -> Types.Expr Types.Storage
rewriteToExpr _ _ (Constant _) state = state
rewriteToExpr layout cid (Rewrite (Update typ i@(Item _ _ ref) e)) state =
  case typ of
    SInteger -> Types.SStore (Types.Lit $ fromIntegral addr) offset e' state
    SBoolean -> Types.SStore (Types.Lit $ fromIntegral addr) offset e' state
    SByteStr -> error "Bytestrings not supported"
    SContract -> error "Contracts not supported"
  where
    (addr, slot) = getSlot layout cid (idFromItem i)
    offset = offsetFromRef slot ref
    e' = toExpr e

returnsToExpr :: Maybe TypedExp -> Types.Expr Types.Buf
returnsToExpr Nothing = Types.ConcreteBuf ""
returnsToExpr (Just r) = typedExpToBuf r

offsetFromRef :: Integer -> StorageRef -> Types.Expr Types.EWord
offsetFromRef slot (SVar _ _ _) = Types.Lit $ fromIntegral slot
offsetFromRef slot (SMapping _ _ ixs) = 
  foldl (\slot i -> Types.keccak ((wordToBuf slot) <> (typedExpToBuf i))) (Types.Lit $ fromIntegral slot) ixs
offsetFromRef _ (SField _ _ _ _) = error "TODO contracts not supported"

wordToBuf :: Types.Expr Types.EWord -> Types.Expr Types.Buf
wordToBuf w = Types.WriteWord (Types.Lit 0) w (Types.ConcreteBuf "")

wordToProp :: Types.Expr Types.EWord -> Types.Prop
wordToProp w = Types.PNeg (Types.PEq w (Types.Lit 0))
  
typedExpToBuf :: TypedExp -> Types.Expr Types.Buf
typedExpToBuf expr =
  case expr of
    TExp styp e -> expToBuf styp e
    
expToBuf :: forall a. SType a -> Exp a  -> Types.Expr Types.Buf
expToBuf styp e =
  case styp of
    SInteger -> Types.WriteWord (Types.Lit 0) (toExpr e) (Types.ConcreteBuf "")
    SBoolean -> Types.WriteWord (Types.Lit 0) (toExpr e) (Types.ConcreteBuf "")
    SByteStr -> toExpr e
    SContract -> error "Internal error: expecting primitive type"

getSlot :: Layout -> Id -> Id -> (Types.Addr, Integer)
getSlot layout cid name =
  case M.lookup cid layout of
    Just m -> case M.lookup name m of
      Just v -> v
      Nothing -> error "Internal error: invalid variable name"
    Nothing -> error "Internal error: invalid contract name"

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

toProp :: Exp ABoolean -> Types.Prop
toProp (And _ e1 e2) = pop2 Types.PAnd e1 e2
toProp (Or _ e1 e2) = pop2 Types.POr e1 e2
toProp (Impl _ e1 e2) = pop2 Types.PImpl e1 e2
toProp (Neg _ e1) = Types.PNeg (toProp e1)
toProp (Syntax.Annotated.LT _ e1 e2) = op2 Types.PLT e1 e2
toProp (LEQ _ e1 e2) = op2 Types.PLEq e1 e2
toProp (GEQ _ e1 e2) = op2 Types.PGEq e1 e2
toProp (Syntax.Annotated.GT _ e1 e2) = op2 Types.PGT e1 e2
toProp (LitBool _ b) = Types.PBool b
toProp (Eq _ SInteger e1 e2) = Types.PEq (toExpr e1) (toExpr e2)
toProp (Eq _ SBoolean e1 e2) = Types.PEq (toExpr e1) (toExpr e2)
toProp (NEq _ SInteger e1 e2) = Types.PNeg $ Types.PEq (toExpr e1) (toExpr e2)
toProp (NEq _ SBoolean e1 e2) = Types.PNeg $ Types.PEq (toExpr e1) (toExpr e2)
toProp (ITE _ _ _ _) = error "Internal error: expecting flat expression"
toProp (Var _ _ _) = error "TODO" -- (Types.Var (T.pack x)) -- vars can only be words? TODO other types
toProp (TEntry _ _ _) = error "TODO" -- Types.SLoad addr idx 

toExpr :: forall a. Exp a -> Types.Expr (ExprType a)
-- booleans
toExpr (And _ e1 e2) = op2 Types.And e1 e2
toExpr (Or _ e1 e2) = op2 Types.Or e1 e2
toExpr (Impl _ e1 e2) = op2 (\x y -> Types.Or (Types.Not x) y) e1 e2
toExpr (Neg _ e1) = Types.Not (toExpr e1)
toExpr (Syntax.Annotated.LT _ e1 e2) = op2 Types.LT e1 e2
toExpr (LEQ _ e1 e2) = op2 Types.LEq e1 e2
toExpr (GEQ _ e1 e2) = op2 Types.GEq e1 e2
toExpr (Syntax.Annotated.GT _ e1 e2) = op2 Types.GT e1 e2
toExpr (LitBool _ b) = Types.Lit (fromIntegral $ fromEnum $ b)
-- integers
toExpr (Add _ e1 e2) = op2 Types.Add e1 e2
toExpr (Sub _ e1 e2) = op2 Types.Sub e1 e2
toExpr (Mul _ e1 e2) = op2 Types.Mul e1 e2
toExpr (Div _ e1 e2) = op2 Types.Div e1 e2
toExpr (Mod _ e1 e2) = op2 Types.Mod e1 e2 -- which mod?
toExpr (Exp _ e1 e2) = op2 Types.Exp e1 e2
toExpr (LitInt _ n) = Types.Lit (fromIntegral n)
toExpr (IntEnv _ env) = ethEnvToWord env
-- bounds
toExpr (IntMin _ n) = Types.Lit (fromIntegral $ intmin n)
toExpr (IntMax _ n) = Types.Lit (fromIntegral $ intmax n)
toExpr (UIntMin _ n) = Types.Lit (fromIntegral $ uintmin n)
toExpr (UIntMax _ n) = Types.Lit (fromIntegral $ uintmax n)
-- bytestrings
toExpr (Cat _ e1 e2) = error "TODO"
toExpr (Slice _ bs start end) = error "TODO"
  -- Types.CopySlice (toExpr start) (Types.Lit 0) -- src and dst offset
  -- (Types.Add (Types.Sub (toExp end) (toExpr start)) (Types.Lit 0)) -- size
  -- (toExpr bs) (Types.ConcreteBuf "") -- src and dst  
toExpr (ByStr _ str) = Types.ConcreteBuf (B8.pack str)
toExpr (ByLit _ bs) = Types.ConcreteBuf bs
toExpr (ByEnv _ env) = ethEnvToBuf env
-- contracts
toExpr (Create _ typ cid args) = error "TODO"
-- polymorphic
toExpr (Eq _ SInteger e1 e2) = Types.Eq (toExpr e1) (toExpr e2)
toExpr (Eq _ SBoolean e1 e2) = Types.Eq (toExpr e1) (toExpr e2)

toExpr (NEq _ SInteger e1 e2) = Types.Not $ Types.Eq (toExpr e1) (toExpr e2)
toExpr (NEq _ SBoolean e1 e2) = Types.Not $ Types.Eq (toExpr e1) (toExpr e2)

toExpr (ITE _ _ _ _) = error "Internal error: expecting flat expression"

toExpr (Var _ SInteger x) = (Types.Var (T.pack x)) -- vars can only be words? TODO other types

-- toExpr (TEntry _ SInteger item) = Types.SLoad addr idx 


-- TODO index is the slot number or the address ?


op2 :: forall a b. (Types.Expr (ExprType b) -> Types.Expr (ExprType b) -> a) -> Exp b -> Exp b -> a
op2 op e1 e2 = op (toExpr e1) (toExpr e2)
  
pop2 :: forall a. (Types.Prop -> Types.Prop -> a) -> Exp ABoolean -> Exp ABoolean -> a
pop2 op e1 e2 = op (toProp e1) (toProp e2)
