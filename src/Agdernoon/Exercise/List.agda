------------------------------------------------------------------------
-- The Agdernoon exercises
--
-- Lists
------------------------------------------------------------------------

module Agdernoon.Exercise.List where

open import Agdernoon.Data.Bool
open import Agdernoon.Data.List hiding (filter)

------------------------------------------------------------------------
-- Exercise. Define the filter function:

filter : ∀ {A} → (A → Bool) → List A → List A
filter _ []       = []
filter p (x ∷ xs) with p x
... | true  = x ∷ filter p xs
... | false = filter p xs
