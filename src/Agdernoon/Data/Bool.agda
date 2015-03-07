------------------------------------------------------------------------
-- The Agdernoon library
--
-- Booleans
------------------------------------------------------------------------

module Agdernoon.Data.Bool where

infixr 6 _∧_
infixr 5 _∨_
infix  0 if_then_else

------------------------------------------------------------------------
-- The boolean type

data Bool : Set where
  true  : Bool
  false : Bool

------------------------------------------------------------------------
-- Some operations

not : Bool → Bool
not true  = false
not false = true

if_then_else : {A : Set} → Bool → A → A → A
if true  then t else _ = t
if false then _ else f = f

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

_∨_ : Bool → Bool → Bool
true  ∨ _ = true
false ∨ b = b
