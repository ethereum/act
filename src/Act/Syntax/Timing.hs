{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}

{-|
Module      : Syntax.Timing
Description : Timing annotations for references to storage variables. In the source code, a 
              reference to a storage variable can be explicitly time with `Pre` or `Post` or 
              implicitly timed (`Neither`). After typing, in a separate `annotate` pass, all
              timing are made explicit.
-}
module Act.Syntax.Timing where

import Data.Char (toLower)

-- | This will never be used as-is. Its only purpose is to use with -XDataKinds,
-- to distinguish between those AST terms which have fully explicit timings ('Timed')
-- and those which have implicit timings.
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

-- | If the supplied time is `Pre`, this returns `pre(input)` (and analogously for `Post`).
-- Otherwise returns the untouched `String`.
timeParens :: Time t -> String -> String
timeParens t s | isTimed t = fmap toLower (show t) <> "(" <> s <> ")"
               | otherwise = s

-- | Types for which all implicit timings can freely be given any explicit timing,
-- i.e. we need context to decide which time it refers to.
class Timable c where
  -- | Takes an 'Untimed' 'Timable' thing and points it towards the prestate.
  setPre :: c Untimed -> c Timed
  setPre = setTime Pre

  -- | Takes an 'Untimed' 'Timeable' thing and points it towards the poststate.
  setPost :: c Untimed -> c Timed
  setPost = setTime Post

  -- | Takes an 'Untimed' 'Timeable' thing and points it towards the given state.
  setTime :: When -> c Untimed -> c Timed

  -- | Defines how an 'Untimed' thing should be given explicit timings.
class Annotatable c where
  annotate :: c Untimed -> c Timed