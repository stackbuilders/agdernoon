------------------------------------------------------------------------
-- The Agdernoon exercises
--
-- Vectors
------------------------------------------------------------------------

module Agdernoon.Exercise.Vec where

open import Agdernoon.Data.Nat
open import Agdernoon.Data.Vec

------------------------------------------------------------------------
-- Exercise. Define the tail function:

tail : ∀ {A n} → Vec A (suc n) → Vec A n
tail (_ ∷ xs) = xs

------------------------------------------------------------------------
-- Exercise. Define the map function:

map : ∀ {A B n} → (A → B) → Vec A n → Vec B n
map _ []       = []
map f (x ∷ xs) = f x ∷ map f xs
