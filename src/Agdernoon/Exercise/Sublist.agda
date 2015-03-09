------------------------------------------------------------------------
-- The Agdernoon exercises
--
-- Lists
------------------------------------------------------------------------

module Agdernoon.Exercise.Sublist where

open import Agdernoon.Data.List

------------------------------------------------------------------------
-- Exercise. Prove the reflexivity of _⊆_:

⊆-refl : ∀ {A} {xs : List A} → xs ⊆ xs
⊆-refl {xs = xs} = {!!}

------------------------------------------------------------------------
-- Exercise. Prove the transitivity of _⊆_:

⊆-trans : ∀ {A} {xs ys zs : List A} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans xs⊆ys ys⊆zs = {!!}
