-- Data types for the Act AST after parsing. It is also equipped with position information
-- for printing informative error messages.
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE InstanceSigs #-}

module Act.Syntax.Untyped (module Act.Syntax.Untyped) where

import Data.Aeson
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty(..), nonEmpty)
import Data.Foldable1
import Data.Validation
import Data.Text as T (pack)

import EVM.ABI
import Act.Lex

type Pn = AlexPosn

type Id = String

newtype Act = Main [Contract]
  deriving (Eq, Show)

data Contract = Contract Constructor [Transition]
  deriving (Eq, Show)

data Constructor = Constructor Pn Id Interface [Pointer] Iff Creates Ensures Invariants
  deriving (Eq, Show)

data Transition = Transition Pn Id Id Interface [Pointer] Iff Cases Ensures
  deriving (Eq, Show)

type Iff = [Expr]

type Ensures = [Expr]

type Invariants = [Expr]

data Pointer = PointsTo Pn Id Id
  deriving (Eq, Ord)

instance Show Pointer where
  show (PointsTo _ x c) = "(" <> x <> "|->" <> c <> ")"

data Interface = Interface Id [Decl]
  deriving (Eq, Ord)

instance Show Interface where
  show (Interface a d) = a <> "(" <> intercalate ", " (fmap show d) <> ")"

newtype Cases = Branches [Case]
  deriving (Eq, Show)

data Case = Case Pn Expr Post
  deriving (Eq, Show)

data Post
  = Post [Storage] (Maybe Expr)
  deriving (Eq, Show)

newtype Creates = Creates [Assign]
  deriving (Eq, Show)

data Storage
  = Update Entry Expr
  deriving (Eq, Show)

data Assign = AssignVal StorageVar Expr | AssignMapping StorageVar [Mapping] | AssignArray StorageVar ExprList
  deriving (Eq, Show)

data StorageVar = StorageVar Pn SlotType Id
  deriving (Eq, Show)

data Decl = Decl AbiType Id
  deriving (Eq, Ord)

data Entry
  = EVar Pn Id
  | EMapping Pn Entry [Expr]
  | EField Pn Entry Id
  deriving (Eq, Show)

data Mapping = Mapping Expr Expr
  deriving (Eq, Show)

data Expr
  = EAnd Pn Expr Expr
  | EOr Pn Expr Expr
  | ENot Pn Expr
  | EImpl Pn Expr Expr
  | EEq Pn Expr Expr
  | ENeq Pn Expr Expr
  | ELEQ Pn Expr Expr
  | ELT Pn Expr Expr
  | EGEQ Pn Expr Expr
  | EGT Pn Expr Expr
  | EAdd Pn Expr Expr
  | ESub Pn Expr Expr
  | EITE Pn Expr Expr Expr
  | EMul Pn Expr Expr
  | EDiv Pn Expr Expr
  | EMod Pn Expr Expr
  | EExp Pn Expr Expr
  | EUTEntry Entry
  | EPreEntry Entry
  | EPostEntry Entry
  | ECreate Pn Id [Expr]
  | ListConst Expr
  | ECat Pn Expr Expr
  | ESlice Pn Expr Expr Expr
  | ENewaddr Pn Expr Expr
  | ENewaddr2 Pn Expr Expr Expr
  | BYHash Pn Expr
  | BYAbiE Pn Expr
  | StringLit Pn String
  | WildExp Pn
  | EnvExp Pn EthEnv
  | IntLit Pn Integer
  | BoolLit Pn Bool
  | EInRange Pn AbiType Expr
  deriving (Eq, Show)

data ValueType
  = ContractType Id
  | PrimitiveType AbiType
  deriving Eq

instance Show ValueType where
  show (ContractType c) = c
  show (PrimitiveType t) = show t

data SlotType
  = StorageMapping (NonEmpty ValueType) ValueType
  | StorageValue ValueType
  deriving (Eq)

instance Show SlotType where
 show (StorageValue t) = show t
 show (StorageMapping s t) =
   foldr
   (\x y ->
       "mapping("
       <> show x
       <> " => "
       <> y
       <> ")")
   (show t) s

data EthEnv
  = Caller
  | Callvalue
  | Calldepth
  | Origin
  | Blockhash
  | Blocknumber
  | Difficulty
  | Chainid
  | Gaslimit
  | Coinbase
  | Timestamp
  | This
  | Nonce
  deriving (Show, Eq)

instance Show Decl where
  show (Decl t a) = show t <> " " <> a

data NestedList p a
  = LeafList (NonEmpty a)
  | NodeList p (NonEmpty (NestedList p a)) 
  deriving (Show, Eq)

instance Functor (NestedList p) where
  fmap f (LeafList l) = LeafList $ fmap f l
  fmap f (NodeList p l) = NodeList p $ (fmap . fmap) f l

instance Foldable (NestedList p) where
  foldr f c (LeafList l) = foldr f c l
  foldr f c (NodeList p (h:|t)) = 
    case nonEmpty t of
      Just net -> foldr f (foldr f c (NodeList p net)) h
      Nothing -> foldr f c h

instance Traversable (NestedList p) where
  traverse f (LeafList l) = fmap LeafList $ traverse f l
  traverse f (NodeList p l) = fmap (NodeList p) $ traverse (traverse f) l

-- | returns list of length at each level, if its consistent for each level
pfctHeight :: (Show p) => NestedList p a -> Validation (NonEmpty (Pn,String)) [Int]
pfctHeight (LeafList l) = pure $ [ length l ]
pfctHeight (NodeList pn l) = foldrMap1 pfctHeight g l `bindValidation` (pure . ((:) (length l)))
  where
    g :: (Show p) => NestedList p a -> Validation (NonEmpty (Pn,String)) [Int] -> Validation (NonEmpty (Pn,String)) [Int]
    g x y = if pfctHeight x == y then y else Failure $ (AlexPn 0 0 0, "Sub-arrays have different sizes at " <> show pn) :| []
-- TODO: current implementation accumulates errors, meaning that for the last
-- level, for each difference -- or maybe not? seems foldrMap1 uses bind ??

    -- printArraySize :: [Int] -> String
    -- printArraySize [] = []
    -- printArraySize (h : t) = concat (printArraySize t) $ "[" <> show h <> "]" 
    -- TODO: try to print where size mismatch happens

-- TODO: consider incomporating below to above
-- toList, and:
flattenedIdxs :: [a] -> [Int] -> [(a,[Int])]
flattenedIdxs l typ = zip l (idxs)
  where
    typeAcc = drop 1 $ scanr (*) 1 typ
    
    idxs = map idx [0..(length l - 1)]
    idx e = map (\(x1,x2) -> (e `div` x2) `mod` x1) $ (zip typ typeAcc)

type ExprList = NestedList Pn Expr

instance ToJSON SlotType where
  toJSON (StorageValue t) = object ["kind" .= String "ValueType"
                                   , "valueType" .= toJSON t]
  toJSON (StorageMapping ixTypes resType) = object [ "kind" .= String "MappingType"
                                                   , "ixTypes" .= toJSON ixTypes
                                                   , "resType" .= toJSON resType]


instance ToJSON ValueType where
  toJSON (ContractType c) = object [ "kind" .= String "ContractType"
                                   , "name" .= show c ]
  toJSON (PrimitiveType abiType) = object [ "kind" .= String "AbiType"
                                          , "abiType" .= toJSON abiType ]


instance ToJSON AbiType where
  toJSON (AbiUIntType n)          = object [ "type" .= String "UInt"
                                           , "size" .= String (T.pack $ show n) ]
  toJSON (AbiIntType n)           = object [ "type" .= String "Int"
                                           , "size" .= String (T.pack $ show n) ]
  toJSON AbiAddressType           = object [ "type" .= String "Address" ]
  toJSON AbiBoolType              = object [ "type" .= String "Bool" ]
  toJSON (AbiBytesType n)         = object [ "type" .= String "Bytes"
                                           , "size" .= String (T.pack $ show n) ]
  toJSON AbiBytesDynamicType      = object [ "type" .= String "BytesDynamic" ]
  toJSON AbiStringType            = object [ "type" .= String "String" ]
  toJSON (AbiArrayDynamicType t)  = object [ "type" .= String "ArrayDynamic"
                                        , "arrayType" .= toJSON t ]
  toJSON (AbiArrayType n t)       = object [ "type" .= String "Array"
                                           , "arrayType" .= toJSON t
                                           , "size" .= String (T.pack $ show n) ]
  toJSON (AbiTupleType ts)        = object [ "type" .= String "Tuple"
                                           , "elemTypes" .= toJSON ts ]
  toJSON (AbiFunctionType)        = object [ "type" .= String "Function" ]



-- Create the string that is used to construct the function selector
makeIface :: Interface -> String
makeIface (Interface a decls) =
 a <> "(" <> intercalate "," (fmap (\(Decl typ _) -> show typ) decls) <> ")"
