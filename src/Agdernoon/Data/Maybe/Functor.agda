------------------------------------------------------------------------
-- The Agdernoon library
--
--
------------------------------------------------------------------------

module Agdernoon.Data.Maybe.Functor where

open import Agdernoon.Category.Functor
open import Agdernoon.Data.Maybe

------------------------------------------------------------------------
--

rawFunctor : RawFunctor Maybe
rawFunctor = record { fmap = fmap }
  where
    fmap : ∀ {A B} → (A → B) → Maybe A → Maybe B
    fmap f (just x) = just (f x)
    fmap _ nothing  = nothing
