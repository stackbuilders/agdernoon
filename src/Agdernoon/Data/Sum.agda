------------------------------------------------------------------------
-- The Agdernoon library
--
-- Sums (disjoint unions)
------------------------------------------------------------------------

module Agdernoon.Data.Sum where

open import Agdernoon.Function

------------------------------------------------------------------------
--

infixr 1 _⊎_

data _⊎_ (A B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

------------------------------------------------------------------------
--

[_,_] : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
[ f , _ ] (inj₁ x) = f x
[ _ , g ] (inj₂ y) = g y

map : ∀ {A B C D} → (A → C) → (B → D) → A ⊎ B → C ⊎ D
map f g =  [ inj₁ ∘ f , inj₂ ∘ g ]
