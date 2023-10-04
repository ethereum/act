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


module HEVM_utils where

import Prelude hiding (GT, LT)

import Data.Containers.ListUtils (nubOrd)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.ByteString as BS
import Control.Monad
import Control.Monad.ST (stToIO)

import Syntax.Annotated
import Syntax.Untyped (makeIface)

import qualified EVM.Types as EVM hiding (Contract(..))
import EVM.Expr hiding (op2, inRange)
import EVM.SymExec hiding (EquivResult, isPartial)
import EVM.Solvers
import qualified EVM.Format as Format
import qualified EVM.Fetch as Fetch


-- TODO move this to HEVM
type Calldata = (EVM.Expr EVM.Buf, [EVM.Prop])
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

-- | decompiles the given EVM bytecode into a list of Expr branches
getRuntimeBranches :: SolverGroup -> BS.ByteString -> Calldata -> IO [EVM.Expr EVM.End]
getRuntimeBranches solvers bs calldata = do
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


-- | decompiles the given EVM initcode into a list of Expr branches
getInitcodeBranches :: SolverGroup -> BS.ByteString -> Calldata -> IO [EVM.Expr EVM.End]
getInitcodeBranches solvers initcode calldata = do  
  initVM <- stToIO $ abstractVM calldata initcode Nothing True
  expr <- interpret (Fetch.oracle solvers Nothing) Nothing 1 StackBased initVM runExpr
  let simpl = if True then (simplify expr) else expr
  -- traceM (T.unpack $ Format.formatExpr simpl)
  let nodes = flattenExpr simpl  
      
  when (any isPartial nodes) $ do
    putStrLn ""
    putStrLn "WARNING: hevm was only able to partially explore the given contract due to the following issues:"
    putStrLn ""
    TIO.putStrLn . T.unlines . fmap (Format.indent 2 . ("- " <>)) . fmap Format.formatPartial . nubOrd $ (getPartials nodes)

  pure nodes
