

instance (Abi a, Abi b, Abi c, Abi d) => Abi (a,b,c,d) where
  abiencode = error ""

instance (Abi a, Abi b, Abi c, Abi d, Abi e) => Abi (a,b,c,d,e) where
  abiencode = error ""

-- class (Cap.HasState name Address m) => HasReference name m where
--   ref :: (IsContract m) => m
-- class IsContract (name :: k) a where
--   implementation :: Proxy# name Contract 


-- class Ref a where
--   address :: Address
  
data Reference (tag :: name) a where
  Construct :: Proxy# tag -> Env -> (a, Address) -> Reference tag a
  Behaviour :: Reference tag a -> (a -> Exe a b) -> Reference tag a

-- class Method (contract :: k) (abi :: v) arg st out where
--   implementation :: (Proxy# contract) -> (Proxy# abi) -> arg -> Contract contract st out

class Export (contract :: k) (abi :: v) arg st out where
  --implementation :: (Proxy# contract) -> (Proxy# abi) -> arg -> Contract contract st out


-- class (Export name method fromIn fromState fromOut) => Import name method fromIn fromState fromOut to toState toOut where
--   call :: Proxy# name -> Proxy# method -> Proxy# to -> Ref a -> (fromIn -> a) -> (fromOut -> Contract to toState toOut)


uncurry4 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry4 f (a,b,c) = f a b c

-- instance Export "Dai" "transferFrom"(Address,Address,Uint) DaiState Bool where
--   implementation _ _ = runDai . (uncurry4 transferFrom)

-- instance Import "Dai" "transferFrom" "Bank" (Address,Address,Uint) DaiState Bool where
--   call _ _ = 

-- | let's see how calling semantics work. consider another simple contract, in Solidity:

{-
contract Bank {
   address Dai public constant = Dai(0xacab);
   mapping(address=>uint) public deposited;
   function deposit(uint amount) public {
      deposited[msg.sender] += amount;
      transferFrom(msg.sender, address(this), amount);
   }
   function withdraw(uint amount) public {
      require(amount <= deposited[msg.sender])
      deposited[msg.sender] -= amount;
      transfer(msg.sender, amount);
   }
}
-}

data BankState = BankState {
  _deposits :: Map Address Uint
  }

call :: Reference (tag :: name) a -> 

makeLenses ''BankState

newtype Bank a = Bank (Exe BankState a)
  deriving (Functor,
            Applicative,
            Monad,
            MonadState BankState,
            MonadError String,
            MonadReader Env
            )

-- deposit :: Uint -> Bank ()
-- deposit amount = do
--   caller <- view (msg.sender)
--   us <- view this
--   deposits . at caller += amount
--   _ <- call 
--   return ()

-- withdraw :: Uint -> Bank ()
-- withdraw amount = do
--   caller <- view (msg.sender)
--   available <- use (deposits . at caller)
--   require (amount <= available) ""
--   us <- view this
--   deposits . at caller -= amount
--   modifying dai (transfer caller amount)


-- class (MonadReader Env m, MonadState a m, MonadError String m, Abi cArg) => IsContract m name a b cArg where
--   address :: Address
--   new :: Env -> cArg -> a
  



data Ref s a = Ref (MutVar# s a)
-- ^ a value of type @STRef s a@ is a mutable variable in state thread @s@,
-- containing a value of type @a@
--
-- >>> :{
-- runST (do
--     ref <- newSTRef "hello"
--     x <- readSTRef ref
--     writeSTRef ref (x ++ "world")
--     readSTRef ref )
-- :}
-- "helloworld"

-- |Build a new 'STRef' in the current state thread
newRef :: Env -> a -> (Exe a (), Address)
newRef currentEnv init = ST $ \s1# ->
    case newMutVar# init s1#            of { (# s2#, var# #) ->
    (# s2#, STRef var# #) }

-- |Write a new value into an 'STRef'
callRef :: STRef s a -> Exe a b
callRef (STRef var#) val = ST $ \s1# ->
    case writeMutVar# var# val s1#      of { s2# ->
    (# s2#, () #) }

-- | Pointer equality.
--
-- @since 2.01
instance Eq (STRef s a) where
    STRef v1# == STRef v2# = isTrue# (sameMutVar# v1# v2#)
