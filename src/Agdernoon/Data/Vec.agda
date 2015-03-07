------------------------------------------------------------------------
-- The Agdernoon library
--
-- Vectors
------------------------------------------------------------------------

module Agdernoon.Data.Vec where

open import Agdernoon.Data.Nat

infixr 5 _∷_

------------------------------------------------------------------------
--

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)
