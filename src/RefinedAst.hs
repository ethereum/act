{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
module RefinedAst where
import GHC.Generics
import Data.Map.Strict    (Map)
import qualified Data.Map.Strict      as Map
import Data.ByteString       (ByteString)

import Syntax

-- AST post typechecking
data Behaviour a = Behaviour
  {_name :: Id,
   _contract :: Id,
   _interface :: (Id, [Decl]),
   _preconditions :: [Exp T_Bool],
   _postconditions :: [Exp T_Bool],
   _cases :: Map (Exp T_Bool) Claim
  }
  --deriving (Eq, Ord, Show, Read)

type Contract = Exp T_Int

--types understood by proving tools
data MType 
  = Integer
  | Boolean
  | ByteStr
  | Mapping (Map MType MType)
--  deriving (Eq, Ord, Show, Read)

--type Claim = (Map Contract [OldStorageUpdate], Maybe (TypedExp))

-- the type var a holds the type of the return expression
data Claim = Claim (Map Contract [StorageUpdate]) (Maybe (ReturnExp))
--  deriving (Eq, Ord, Show, Read)

--type OldStorageUpdate = (Entry, TypedExp)


-- meta types that work as GADT "tags"
--data MType = Int T_Int | Bool T_Bool | Mapp Mapping k a
data T_Int
data T_Bool
data T_Bytes
data T_List t
data T_Tuple
data Mapping a b

--token = [("totalSupply", Integer), ("balanceOf", Map Integer Integer)]

--updates = [("totalSupply", VarInt
data StorageUpdate
  = IntUpdate (TEntry T_Int) (Exp T_Int)
  | BoolUpdate (TEntry T_Bool) (Exp T_Bool)
  | BytesUpdate (TEntry T_Bytes) (Exp T_Bytes)
--  deriving (Eq, Ord, Show, Read)

--totalSupply[msg.sender] => Exp T_Int

--Map Id MType

data TContainer t where --
  DirectInt    :: TContainer T_Int
  DirectBool   :: TContainer T_Bool
  DirectBytes  :: TContainer T_Bytes
  IntIndexed   :: TContainer T_Int -> TContainer t -> TContainer (Mapping T_Int t)
  BoolIndexed  :: TContainer T_Int -> TContainer t -> TContainer (Mapping T_Int t)
  BytesIndexed :: TContainer T_Int -> TContainer t -> TContainer (Mapping T_Int t)
deriving instance Show (TContainer t)

--   Direct ::  Id -> Container t
-- --  Mapping :: Id -> Container (a -> b)
-- deriving instance Show (Container t)

data TEntry t where
  Simple :: TContainer t -> TEntry t
  Lookup :: TContainer (Mapping a b) -> Exp a -> TEntry b
deriving instance Show (TEntry t)

-- data TEntry a where
--   IntEntry  :: TEntry 'Integer
--   BoolEntry :: TEntry 'Boolean
--   LookEntry :: 'Mapp a b c -> Exp b -> TEntry c
-- data MType typ where 
--   Integer  :: MType T_Int
--   Boolean  :: MType T_Bool
--   MapContainer  :: TEntry a -> TEntry b -> TEntry (Mapping a b)
-- --  MapEntry     :: forall k a. Id -> TEntry (Mapping k a)
--   TLookup    :: (TEntry (Mapping k a)) -> (Exp k) -> TEntry a

--deriving instance Show (TEntry t)
--  Struct  :: (TEntry (Mapping k a)) -> (TExp k) -> TEntry a

-- data TExp typ where
--   Int  :: IExp -> TExp T_Int
--   Bool :: BExp -> TExp T_Bool
--   List :: [TExp t] -> TExp (T_List t)
--  deriving (Show)

-- typed expressions
data Exp t where
  --booleans
  And  :: Exp T_Bool -> Exp T_Bool -> Exp T_Bool
  Or   :: Exp T_Bool -> Exp T_Bool -> Exp T_Bool
  Impl :: Exp T_Bool -> Exp T_Bool -> Exp T_Bool
  Eq  :: Exp t -> Exp t -> Exp T_Bool
  Neg :: Exp T_Bool -> Exp T_Bool
  LE :: Exp T_Int -> Exp T_Int -> Exp T_Bool
  GE :: Exp T_Int -> Exp T_Int -> Exp T_Bool
  LitBool :: Bool -> Exp T_Bool
  BVar :: Id -> Exp T_Bool
  -- integers
  Add :: Exp T_Int -> Exp T_Int -> Exp T_Int
  Sub :: Exp T_Int -> Exp T_Int -> Exp T_Int
  Mul :: Exp T_Int -> Exp T_Int -> Exp T_Int
  Div :: Exp T_Int -> Exp T_Int -> Exp T_Int
  Mod :: Exp T_Int -> Exp T_Int -> Exp T_Int
  Exp :: Exp T_Int -> Exp T_Int -> Exp T_Int
  LitInt :: Int -> Exp T_Int
  IntVar :: Id -> Exp T_Int
  IntEnv :: EthEnv -> Exp T_Int
  -- bytestrings
  Cat :: Exp T_Bytes -> Exp T_Bytes -> Exp T_Bytes
  Slice :: Exp T_Bytes -> Exp T_Int -> Exp T_Int -> Exp T_Bytes
  ByVar :: Id -> Exp T_Bytes
  ByStr :: String -> Exp T_Bytes
  ByLit :: ByteString -> Exp T_Bytes
  --polymorphic
  ITE :: Exp T_Bool -> Exp t -> Exp t
  
deriving instance Show (Exp t)

data ReturnExp
  = ExpInt    (Exp T_Int)
  | ExpBool   (Exp T_Bool)
  | ExpTuple  (Exp T_Tuple)
--  | List      Exp T_List
  

-- data TypedExp
--   = BoolExp BExp
--   | IntExp  IExp
--   | ByteExp ByExp
--   | TupleExp TypedExp TypedExp
--   | ListExp [TypedExp]
--   deriving (Eq, Ord, Show, Read)


-- data BExp
--     = And  BExp BExp
--     | Or   BExp BExp
--     | Impl BExp BExp
--     | IEq  IExp IExp
--     | INEq IExp IExp
--     | YEq  ByExp ByExp
--     | Neg  BExp
--     | LE   IExp IExp
--     | GE   IExp IExp
--     | LEQ  IExp IExp
--     | GEQ  IExp IExp
--     | BTrue
--     | BFalse
--     | BoolVar Id
--   deriving (Eq, Ord, Show, Read)

-- data IExp
--     = Add IExp IExp
--     | Sub IExp IExp
--     | ITE BExp IExp IExp
--     | Mul IExp IExp
--     | Div IExp IExp
--     | Mod IExp IExp
--     | Exp IExp IExp
--     | Lit Integer
--     | IEnv EthEnv
--     | IntVar Id
--   deriving (Eq, Ord, Show, Read)

-- data ByExp
--     = Cat ByExp ByExp
--     | Slice ByExp IExp IExp
--     | ByVar Id
--     | ByStr String
--     | ByLit ByteString
--   deriving (Eq, Ord, Show, Read)

-- add array MTypes and post conditions
