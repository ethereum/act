{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstrainedClassMethods #-}

{-|
Module      : Syntax.Timing
Description : Stuff relating to explicit and implicit references to pre-/post-states.

Do not import directly! If you're doing AST refinement, everything you need is
reexported by "Syntax.TimingAgnostic". If you're doing code generation, everything
you need is reexported by "Syntax.Refined".
-}
module Syntax.Timing where

import Data.Char (toLower)
import Data.Typeable ((:~:)(..))

-- | This will never be used as-is. Its only purpose is to use with -XDataKinds,
-- to ensure type safety of the `Exp` and `TStorageItem` types.
data Timing = Timed | Untimed

-- | Encodes choice between explicitly referring to the pre-/post-state, or not.
data Time t where
  Pre     :: Time Timed
  Post    :: Time Timed
  Neither :: Time Untimed
deriving instance Eq (Time t)
deriving instance Show (Time t)

-- | Encodes choice between referencing the pre- or the poststate.
type When = Time Timed

-- | True iff the input is `Pre` or `Post`.
isTimed :: Time t -> Bool
isTimed Neither = False
isTimed _       = True

proveTiming :: Time t -> Either (t :~: Timed) (t :~: Untimed)
proveTiming Neither = Right Refl
proveTiming Pre     = Left  Refl
proveTiming Post    = Left  Refl

-- | If the supplied time is `Pre`, this returns `pre(input)` (and analogously for `Post`).
-- Otherwise returns the untouched `String`.
timeParens :: Time t -> String -> String
timeParens t s | isTimed t = fmap toLower (show t) <> "(" <> s <> ")"
               | otherwise = s

-- | Types for which any implicit timings are always known and can be made explicit.
class Refinable c where
  -- | Defines how an 'Untimed' thing should be given explicit timings.
  refine :: c Untimed -> c Timed

-- | Types for which all implicit timings can freely be given any explicit timing.
class Timable c where
  -- | Takes an `Untimed` `Timeable` thing and points it towards the prestate.
  setPre :: c Untimed -> c Timed
  setPre = setTime Pre

  -- | Takes an `Untimed` `Timeable` thing and points it towards the poststate.
  setPost :: c Untimed -> c Timed
  setPost = setTime Post

  -- | Takes an `Untimed` `Timeable` thing and points it towards the given state.
  setTime :: When -> c Untimed -> c Timed

  -- -- | Dangerous! Do not use this during code generation, as doing so
  -- -- may damage your AST by replacing valid 'Post' entries with 'Pre'
  -- -- or vice versa. Instead, use 'as' or 'setTime', which provide
  -- -- "the same" functionality but restricted to be type safe.
  -- -- This is the reason why you shouldn't import this module directly.
  -- forceTime :: Time t -> c t0 -> c t

  -- -- | Compare two timeable things for equality while ignoring their timings.
  -- eqModTime :: Eq (c Untimed) => c t -> c u -> Bool
  -- eqModTime a b = forceTime Neither a == forceTime Neither b
