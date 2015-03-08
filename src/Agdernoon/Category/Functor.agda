------------------------------------------------------------------------
-- The Agdernoon library
--
-- Functors
------------------------------------------------------------------------

module Agdernoon.Category.Functor where

------------------------------------------------------------------------
--

record RawFunctor (F : Set → Set) : Set₁ where
  infixl 4 _<$>_

  field
    fmap : ∀ {A B} → (A → B) → F A → F B

  _<$>_ : ∀ {A B} → (A → B) → F A → F B
  _<$>_ = fmap
