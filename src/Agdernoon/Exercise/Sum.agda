------------------------------------------------------------------------
-- The Agdernoon exercises
--
-- Sums (disjoint unions)
------------------------------------------------------------------------

module Agdernoon.Exercise.Sum where

open import Agdernoon.Data.Sum hiding ([_,_])

------------------------------------------------------------------------
-- Exercise (Bove and Dybjer 2009, p. 68). Define the [_,_] function:

[_,_] : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
[_,_] = {!!}
