------------------------------------------------------------------------
-- The Agdernoon library
--
-- Products
------------------------------------------------------------------------

module Agdernoon.Data.Product where

infixr 4 _,_
infixr 2 _×_

------------------------------------------------------------------------
--

data _×_ (A B : Set) : Set where
  _,_ : (x : A) (y : B) → A × B

proj₁ : ∀ {A B} → A × B → A
proj₁ (x , _) = x

proj₂ : ∀ {A B} → A × B → B
proj₂ (_ , y) = y
