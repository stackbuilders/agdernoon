------------------------------------------------------------------------
-- The Agdernoon exercises
--
--
------------------------------------------------------------------------

module Agdernoon.Exercise.List where

open import Agdernoon.Data.Bool
open import Agdernoon.Data.List hiding (filter)

------------------------------------------------------------------------
-- Exercise. Define the filter function:

filter : ∀ {A} → (A → Bool) → List A → List A
filter p xs = {!!}
