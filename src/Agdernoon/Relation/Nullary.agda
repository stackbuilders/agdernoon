------------------------------------------------------------------------
-- The Agdernoon library
--
-- Nullary relations
------------------------------------------------------------------------

module Agdernoon.Relation.Nullary where

open import Agdernoon.Data.Empty

------------------------------------------------------------------------
-- Negation

infix  3 ¬_

¬_ : Set → Set
¬ P = P → ⊥
