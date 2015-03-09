------------------------------------------------------------------------
-- The Agdernoon exercises
--
-- Booleans
------------------------------------------------------------------------

module Agdernoon.Exercise.Bool where

open import Agdernoon.Data.Bool hiding (_∨_)

infixr 5 _∨_

------------------------------------------------------------------------
-- Exercise. Define the _∨_ function:

_∨_ : Bool → Bool → Bool
true  ∨ _ = true
false ∨ b = b
