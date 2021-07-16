--{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
--{-# LANGUAGE DataKinds #-}
--{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
--{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
--{-# Language MultiParamTypeClasses #-}
--{-# Language FlexibleContexts #-}
--{-# Language ScopedTypeVariables #-}
--{-# LANGUAGE TypeFamilies #-}
--{-# Language TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}


module Syntax.Refined (module Syntax.Refined) where

import Data.Aeson
import Data.Aeson.Types
import Data.List (nub)
import Data.Text (pack)
import Data.Typeable
import Data.Vector (fromList)

import Syntax.TimeAgnostic as Syntax.Refined hiding (Claim,Transition,Invariant,InvariantPred,Constructor,Behaviour,Rewrite,StorageUpdate,StorageLocation,TStorageItem,Exp,TypedExp)
import Syntax.TimeAgnostic as Syntax.Refined (pattern Invariant, pattern Constructor, pattern Behaviour, pattern Rewrite, pattern Exp)
import qualified Syntax.TimeAgnostic as Agnostic

import Syntax.Timing as Syntax.Refined hiding (Timing(..),Timable,Time)
import Syntax.Timing

type Claim           = Agnostic.Claim           Timed
type Transition      = Agnostic.Transition      Timed
type Invariant       = Agnostic.Invariant       Timed
type InvariantPred   = Agnostic.InvariantPred   Timed
type Constructor     = Agnostic.Constructor     Timed
type Behaviour       = Agnostic.Behaviour       Timed
type Rewrite         = Agnostic.Rewrite         Timed
type StorageUpdate   = Agnostic.StorageUpdate   Timed
type StorageLocation = Agnostic.StorageLocation Timed
type TStorageItem a  = Agnostic.TStorageItem  a Timed
type Exp          a  = Agnostic.Exp           a Timed
type TypedExp        = Agnostic.TypedExp        Timed

instance Refinable Agnostic.Claim where
  refine claim = case claim of
    C ctor -> C $ refine ctor
    B behv -> B $ refine behv
    I invr -> I $ refine invr
    S stor -> S stor

instance Refinable Agnostic.Transition where
  refine trans = case trans of
    Ctor ctor -> Ctor $ refine ctor
    Behv behv -> Behv $ refine behv

instance Refinable Agnostic.Invariant where
  refine inv@Invariant{..} = inv
    { _ipreconditions = setPre <$> _ipreconditions
    , _istoragebounds = setPre <$> _istoragebounds -- not 100% on this `setPre`
    , _predicate      = (setPre _predicate, setPost _predicate)
    }

instance Refinable Agnostic.Constructor where
  refine ctor@Constructor{..} = ctor
    { _cpreconditions = setPre <$> _cpreconditions
    , _initialStorage = refine <$> _initialStorage
    , _cstateUpdates  = refine <$> _cstateUpdates
    }

instance Refinable Agnostic.Behaviour where
  refine behv@Behaviour{..} = behv
    { _preconditions = setPre <$> _preconditions
    , _stateUpdates  = refine <$> _stateUpdates
    }

instance Refinable Agnostic.Rewrite where
  refine (Constant location) = Constant $ setPre location
  refine (Rewrite  update)   = Rewrite  $ refine update

instance Refinable Agnostic.StorageUpdate where
  refine update = case update of
    IntUpdate item expr -> IntUpdate (setPost item) (setPre expr) -- not 100% on these `setPost`
    BoolUpdate item expr -> BoolUpdate (setPost item) (setPre expr)
    BytesUpdate item expr -> BytesUpdate (setPost item) (setPre expr)

instance Timable Agnostic.StorageLocation where
  setTime time location = case location of
    IntLoc item -> IntLoc $ setTime time item
    BoolLoc item -> BoolLoc $ setTime time item
    BytesLoc item -> BytesLoc $ setTime time item

instance Timable Agnostic.TypedExp where
  setTime time texp = case texp of
    ExpInt expr -> ExpInt $ setTime time expr
    ExpBool expr -> ExpBool $ setTime time expr
    ExpBytes expr -> ExpBytes $ setTime time expr

instance Timable (Agnostic.Exp a) where
  setTime time expr = case expr of
    -- booleans
    And  x y -> And (go x) (go y)
    Or   x y -> Or (go x) (go y)
    Impl x y -> Impl (go x) (go y)
    Neg x -> Neg (go x)
    LE x y -> LE (go x) (go y)
    LEQ x y -> LEQ (go x) (go y)
    GEQ x y -> GEQ (go x) (go y)
    GE x y -> GE (go x) (go y)
    LitBool x -> LitBool x
    BoolVar x -> BoolVar x
    -- integers
    Add x y -> Add (go x) (go y)
    Sub x y -> Sub (go x) (go y)
    Mul x y -> Mul (go x) (go y)
    Div x y -> Div (go x) (go y)
    Mod x y -> Mod (go x) (go y)
    Exp x y -> Exp (go x) (go y)
    LitInt x -> LitInt x
    IntVar x -> IntVar x
    IntEnv x -> IntEnv x
    -- bounds
    IntMin x -> IntMin x
    IntMax x -> IntMax x
    UIntMin x -> UIntMin x
    UIntMax x -> UIntMax x
    -- bytestrings
    Cat x y -> Cat (go x) (go y)
    Slice x y z -> Slice (go x) (go y) (go z)
    ByVar x -> ByVar x
    ByStr x -> ByStr x
    ByLit x -> ByLit x
    ByEnv x -> ByEnv x
    -- builtins
    NewAddr x y -> NewAddr (go x) (go y) 
    -- polymorphic
    Eq  x y -> Eq  (go x) (go y)
    NEq x y -> NEq (go x) (go y)
    ITE x y z -> ITE (go x) (go y) (go z)
    TEntry item _ -> TEntry (go item) time
    where
      go :: Timable c => c Untimed -> c Timed
      go = setTime time

instance Timable (Agnostic.TStorageItem a) where
  setTime time item = case item of
    IntItem   c x ixs -> IntItem   c x $ setTime time <$> ixs
    BoolItem  c x ixs -> BoolItem  c x $ setTime time <$> ixs
    BytesItem c x ixs -> BytesItem c x $ setTime time <$> ixs

-------------------------------------------------------
-- * Data extraction functions for code generation * --
-------------------------------------------------------

locsFromBehaviour :: Behaviour -> [StorageLocation]
locsFromBehaviour (Behaviour _ _ _ _ preconds postconds rewrites returns) = nub $
  concatMap locsFromExp preconds
  <> concatMap locsFromExp postconds
  <> concatMap locsFromRewrite rewrites
  <> maybe [] locsFromTypedExp returns

locsFromConstructor :: Constructor -> [StorageLocation]
locsFromConstructor (Constructor _ _ _ pre post initialStorage rewrites) = nub $
  concatMap locsFromExp pre
  <> concatMap locsFromExp post
  <> concatMap locsFromRewrite rewrites
  <> concatMap locsFromRewrite (Rewrite <$> initialStorage)

locsFromRewrite :: Rewrite -> [StorageLocation]
locsFromRewrite update = nub $ case update of
  Constant loc -> [loc]
  Rewrite (IntUpdate item e) -> IntLoc item : locsFromExp e
  Rewrite (BoolUpdate item e) -> BoolLoc item : locsFromExp e
  Rewrite (BytesUpdate item e) -> BytesLoc item : locsFromExp e

-- locsFromTypedExp :: TypedExp -> [StorageLocation]
-- locsFromTypedExp (ExpInt e) = locsFromExp e
-- locsFromTypedExp (ExpBool e) = locsFromExp e
-- locsFromTypedExp (ExpBytes e) = locsFromExp e

-- locsFromExp :: Exp a -> [StorageLocation]
-- locsFromExp = nub . go
--   where
--     go :: Exp a -> [StorageLocation]
--     go e = case e of
--       And a b   -> go a <> go b
--       Or a b    -> go a <> go b
--       Impl a b  -> go a <> go b
--       Eq a b    -> go a <> go b
--       LE a b    -> go a <> go b
--       LEQ a b   -> go a <> go b
--       GE a b    -> go a <> go b
--       GEQ a b   -> go a <> go b
--       NEq a b   -> go a <> go b
--       Neg a     -> go a
--       Add a b   -> go a <> go b
--       Sub a b   -> go a <> go b
--       Mul a b   -> go a <> go b
--       Div a b   -> go a <> go b
--       Mod a b   -> go a <> go b
--       Exp a b   -> go a <> go b
--       Cat a b   -> go a <> go b
--       Slice a b c -> go a <> go b <> go c
--       ByVar _ -> []
--       ByStr _ -> []
--       ByLit _ -> []
--       LitInt _  -> []
--       IntMin _  -> []
--       IntMax _  -> []
--       UIntMin _ -> []
--       UIntMax _ -> []
--       IntVar _  -> []
--       LitBool _ -> []
--       BoolVar _ -> []
--       NewAddr a b -> go a <> go b
--       IntEnv _ -> []
--       ByEnv _ -> []
--       ITE x y z -> go x <> go y <> go z
--       TEntry a _ -> locsFromStorageItem a

--     locsFromStorageItem :: TStorageItem a -> [StorageLocation]
--     locsFromStorageItem t = case t of
--       IntItem contract name ixs -> [IntLoc $ IntItem contract name $ ixs] <> ixLocs ixs
--       BoolItem contract name ixs -> [BoolLoc $ BoolItem contract name $ ixs] <> ixLocs ixs
--       BytesItem contract name ixs -> [BytesLoc $ BytesItem contract name $ ixs] <> ixLocs ixs
--       where
--         ixLocs :: [TypedExp] -> [StorageLocation]
--         ixLocs = concatMap locsFromTypedExp

-- ethEnvFromBehaviour :: Behaviour -> [EthEnv]
-- ethEnvFromBehaviour (Behaviour _ _ _ _ preconds postconds rewrites returns) = nub $
--   concatMap ethEnvFromExp preconds
--   <> concatMap ethEnvFromExp postconds
--   <> concatMap ethEnvFromRewrite rewrites
--   <> maybe [] ethEnvFromTypedExp returns

-- ethEnvFromConstructor :: Constructor -> [EthEnv]
-- ethEnvFromConstructor (Constructor _ _ _ pre post initialStorage rewrites) = nub $
--   concatMap ethEnvFromExp pre
--   <> concatMap ethEnvFromExp post
--   <> concatMap ethEnvFromRewrite rewrites
--   <> concatMap ethEnvFromRewrite (Rewrite <$> initialStorage)

-- ethEnvFromRewrite :: Rewrite -> [EthEnv]
-- ethEnvFromRewrite rewrite = case rewrite of
--   Constant (IntLoc item) -> ethEnvFromItem item
--   Constant (BoolLoc item) -> ethEnvFromItem item
--   Constant (BytesLoc item) -> ethEnvFromItem item
--   Rewrite (IntUpdate item e) -> nub $ ethEnvFromItem item <> ethEnvFromExp e
--   Rewrite (BoolUpdate item e) -> nub $ ethEnvFromItem item <> ethEnvFromExp e
--   Rewrite (BytesUpdate item e) -> nub $ ethEnvFromItem item <> ethEnvFromExp e

-- ethEnvFromItem :: TStorageItem a -> [EthEnv]
-- ethEnvFromItem = nub . concatMap ethEnvFromTypedExp . ixsFromItem

-- ethEnvFromTypedExp :: TypedExp -> [EthEnv]
-- ethEnvFromTypedExp (ExpInt e) = ethEnvFromExp e
-- ethEnvFromTypedExp (ExpBool e) = ethEnvFromExp e
-- ethEnvFromTypedExp (ExpBytes e) = ethEnvFromExp e

-- ethEnvFromExp :: Exp a -> [EthEnv]
-- ethEnvFromExp = nub . go
--   where
--     go :: Exp a -> [EthEnv]
--     go e = case e of
--       And a b   -> go a <> go b
--       Or a b    -> go a <> go b
--       Impl a b  -> go a <> go b
--       Eq a b    -> go a <> go b
--       LE a b    -> go a <> go b
--       LEQ a b   -> go a <> go b
--       GE a b    -> go a <> go b
--       GEQ a b   -> go a <> go b
--       NEq a b   -> go a <> go b
--       Neg a     -> go a
--       Add a b   -> go a <> go b
--       Sub a b   -> go a <> go b
--       Mul a b   -> go a <> go b
--       Div a b   -> go a <> go b
--       Mod a b   -> go a <> go b
--       Exp a b   -> go a <> go b
--       Cat a b   -> go a <> go b
--       Slice a b c -> go a <> go b <> go c
--       ITE a b c -> go a <> go b <> go c
--       ByVar _ -> []
--       ByStr _ -> []
--       ByLit _ -> []
--       LitInt _  -> []
--       IntVar _  -> []
--       LitBool _ -> []
--       BoolVar _ -> []
--       IntMin _ -> []
--       IntMax _ -> []
--       UIntMin _ -> []
--       UIntMax _ -> []
--       NewAddr a b -> go a <> go b
--       IntEnv a -> [a]
--       ByEnv a -> [a]
--       TEntry a _ -> ethEnvFromItem a

idFromRewrite :: Rewrite -> Id
idFromRewrite = onRewrite idFromLocation idFromUpdate

idFromItem :: TStorageItem a -> Id
idFromItem (IntItem _ name _) = name
idFromItem (BoolItem _ name _) = name
idFromItem (BytesItem _ name _) = name

idFromUpdate :: StorageUpdate -> Id
idFromUpdate (IntUpdate   item _) = idFromItem item
idFromUpdate (BoolUpdate  item _) = idFromItem item
idFromUpdate (BytesUpdate item _) = idFromItem item

idFromLocation :: StorageLocation -> Id
idFromLocation (IntLoc   item) = idFromItem item
idFromLocation (BoolLoc  item) = idFromItem item
idFromLocation (BytesLoc item) = idFromItem item

contractFromRewrite :: Rewrite -> Id
contractFromRewrite = onRewrite contractFromLoc contractFromUpdate

contractFromItem :: TStorageItem a -> Id
contractFromItem (IntItem c _ _) = c
contractFromItem (BoolItem c _ _) = c
contractFromItem (BytesItem c _ _) = c

-- ixsFromItem :: TStorageItem a -> [TypedExp]
-- ixsFromItem (IntItem   _ _ ixs) = ixs
-- ixsFromItem (BoolItem  _ _ ixs) = ixs
-- ixsFromItem (BytesItem _ _ ixs) = ixs

contractsInvolved :: Behaviour -> [Id]
contractsInvolved = fmap contractFromRewrite . _stateUpdates

contractFromLoc :: StorageLocation -> Id
contractFromLoc (IntLoc item) = contractFromItem item
contractFromLoc (BoolLoc item) = contractFromItem item
contractFromLoc (BytesLoc item) = contractFromItem item

contractFromUpdate :: StorageUpdate -> Id
contractFromUpdate (IntUpdate item _) = contractFromItem item
contractFromUpdate (BoolUpdate item _) = contractFromItem item
contractFromUpdate (BytesUpdate item _) = contractFromItem item

ixsFromLocation :: StorageLocation -> [TypedExp]
ixsFromLocation (IntLoc item) = ixsFromItem item
ixsFromLocation (BoolLoc item) = ixsFromItem item
ixsFromLocation (BytesLoc item) = ixsFromItem item

ixsFromUpdate :: StorageUpdate -> [TypedExp]
ixsFromUpdate (IntUpdate item _) = ixsFromItem item
ixsFromUpdate (BoolUpdate item _) = ixsFromItem item
ixsFromUpdate (BytesUpdate item _) = ixsFromItem item

ixsFromRewrite :: Rewrite -> [TypedExp]
ixsFromRewrite = onRewrite ixsFromLocation ixsFromUpdate

itemType :: TStorageItem a -> MType
itemType IntItem{}   = Integer
itemType BoolItem{}  = Boolean
itemType BytesItem{} = ByteStr

isMapping :: StorageLocation -> Bool
isMapping = not . null . ixsFromLocation

updatesFromRewrites :: [Rewrite] -> [StorageUpdate]
updatesFromRewrites rs = [u | Rewrite u <- rs]

locsFromRewrites :: [Rewrite] -> [StorageLocation]
locsFromRewrites rs = [l | Constant l <- rs]

------------------------
-- * JSON machinery * --
------------------------

instance ToJSON Claim where
  toJSON (S storages) = object [ "kind" .= String "Storages"
                               , "storages" .= toJSON storages]
  toJSON (I (Invariant {..})) = object [ "kind" .= String "Invariant"
                                       , "predicate" .= toJSON _predicate
                                       , "preconditions" .= toJSON _ipreconditions
                                       , "storagebounds" .= toJSON _istoragebounds
                                       , "contract" .= _icontract]
  toJSON (C (Constructor {..})) = object  [ "kind" .= String "Constructor"
                                          , "contract" .= _cname
                                          , "mode" .= (String . pack $ show _cmode)
                                          , "interface" .= (String . pack $ show _cinterface)
                                          , "preConditions" .= toJSON _cpreconditions
                                          , "postConditions" .= toJSON _cpostconditions
                                          , "storage" .= toJSON _initialStorage
                                          ]
  toJSON (B (Behaviour {..})) = object  [ "kind" .= String "Behaviour"
                                        , "name" .= _name
                                        , "contract" .= _contract
                                        , "mode" .= (String . pack $ show _mode)
                                        , "interface" .= (String . pack $ show _interface)
                                        , "preConditions" .= toJSON _preconditions
                                        , "postConditions" .= toJSON _postconditions
                                        , "stateUpdates" .= toJSON _stateUpdates
                                        , "returns" .= toJSON _returns]

--instance ToJSON InvariantPred where
--  toJSON = toJSON . predicate

instance ToJSON Rewrite where
  toJSON (Constant a) = object [ "Constant" .= toJSON a ]
  toJSON (Rewrite a) = object [ "Rewrite" .= toJSON a ]

instance ToJSON StorageLocation where
  toJSON (IntLoc a) = object ["location" .= toJSON a]
  toJSON (BoolLoc a) = object ["location" .= toJSON a]
  toJSON (BytesLoc a) = object ["location" .= toJSON a]

instance ToJSON StorageUpdate where
  toJSON (IntUpdate a b) = object ["location" .= toJSON a ,"value" .= toJSON b]
  toJSON (BoolUpdate a b) = object ["location" .= toJSON a ,"value" .= toJSON b]
  toJSON (BytesUpdate a b) = object ["location" .= toJSON a ,"value" .= toJSON b]

instance ToJSON (TStorageItem a) where
  toJSON (IntItem a b []) = object ["sort" .= pack "int"
                                  , "name" .= String (pack a <> "." <> pack b)]
  toJSON (BoolItem a b []) = object ["sort" .= pack "bool"
                                   , "name" .= String (pack a <> "." <> pack b)]
  toJSON (BytesItem a b []) = object ["sort" .= pack "bytes"
                                    , "name" .= String (pack a <> "." <> pack b)]
  toJSON (IntItem a b c) = mapping a b c
  toJSON (BoolItem a b c) = mapping a b c
  toJSON (BytesItem a b c) = mapping a b c

instance ToJSON TypedExp where
   toJSON (ExpInt a) = object ["sort" .= pack "int"
                              ,"expression" .= toJSON a]
   toJSON (ExpBool a) = object ["sort" .= String (pack "bool")
                               ,"expression" .= toJSON a]
   toJSON (ExpBytes a) = object ["sort" .= String (pack "bytestring")
                                ,"expression" .= toJSON a]

instance Typeable a => ToJSON (Exp a) where
  toJSON (Add a b) = symbol "+" a b
  toJSON (Sub a b) = symbol "-" a b
  toJSON (Exp a b) = symbol "^" a b
  toJSON (Mul a b) = symbol "*" a b
  toJSON (Div a b) = symbol "/" a b
  toJSON (NewAddr a b) = symbol "newAddr" a b
  toJSON (IntVar a) = String $ pack a
  toJSON (LitInt a) = toJSON $ show a
  toJSON (IntMin a) = toJSON $ show $ intmin a
  toJSON (IntMax a) = toJSON $ show $ intmax a
  toJSON (UIntMin a) = toJSON $ show $ uintmin a
  toJSON (UIntMax a) = toJSON $ show $ uintmax a
  toJSON (IntEnv a) = String $ pack $ show a
  toJSON (TEntry a t) = object [ "when".= show t
                               , "ref" .= toJSON a ]
  toJSON (ITE a b c) = object [  "symbol"   .= pack "ite"
                              ,  "arity"    .= Data.Aeson.Types.Number 3
                              ,  "args"     .= Array (fromList [toJSON a, toJSON b, toJSON c])]
  toJSON (And a b)  = symbol "and" a b
  toJSON (Or a b)   = symbol "or" a b
  toJSON (LE a b)   = symbol "<" a b
  toJSON (GE a b)   = symbol ">" a b
  toJSON (Impl a b) = symbol "=>" a b
  toJSON (NEq a b)  = symbol "=/=" a b
  toJSON (Eq a b)   = symbol "==" a b
  toJSON (LEQ a b)  = symbol "<=" a b
  toJSON (GEQ a b)  = symbol ">=" a b
  toJSON (LitBool a) = String $ pack $ show a
  toJSON (BoolVar a) = toJSON a
  toJSON (Neg a) = object [  "symbol"   .= pack "not"
                          ,  "arity"    .= Data.Aeson.Types.Number 1
                          ,  "args"     .= Array (fromList [toJSON a])]

  toJSON (Cat a b) = symbol "cat" a b
  toJSON (Slice s a b) = object [ "symbol" .= pack "slice"
                                , "arity"  .= Data.Aeson.Types.Number 3
                                , "args"   .= Array (fromList [toJSON s, toJSON a, toJSON b])
                                ]
  toJSON (ByVar a) = toJSON a
  toJSON (ByStr a) = toJSON a
  toJSON (ByLit a) = String . pack $ show a
  toJSON (ByEnv a) = String . pack $ show a
  toJSON v = error $ "todo: json ast for: " <> show v

mapping :: (ToJSON a1, ToJSON a2, ToJSON a3) => a1 -> a2 -> a3 -> Value
mapping c a b = object [  "symbol"   .= pack "lookup"
                       ,  "arity"    .= Data.Aeson.Types.Number 3
                       ,  "args"     .= Array (fromList [toJSON c, toJSON a, toJSON b])]

symbol :: (ToJSON a1, ToJSON a2) => String -> a1 -> a2 -> Value
symbol s a b = object [  "symbol"   .= pack s
                      ,  "arity"    .= Data.Aeson.Types.Number 2
                      ,  "args"     .= Array (fromList [toJSON a, toJSON b])]

intmin :: Int -> Integer
intmin a = negate $ 2 ^ (a - 1)

intmax :: Int -> Integer
intmax a = 2 ^ (a - 1) - 1

uintmin :: Int -> Integer
uintmin _ = 0

uintmax :: Int -> Integer
uintmax a = 2 ^ a - 1
