------------------------------------------------------------------------
-- The Agdernoon sessions
--
-- 1 (2015/03/12)
------------------------------------------------------------------------

module Agdernoon.Session.Agdernoon-20150312 where

------------------------------------------------------------------------
-- Booleans
------------------------------------------------------------------------

import Agdernoon.Data.Bool

data Bool : Set where
  false : Bool
  true  : Bool

not : Bool → Bool
not = {!!}

infixr 6 _∧_
infixr 5 _∨_

_∧_ : Bool → Bool → Bool
false ∧ _ = false
true  ∧ b = b

-- C-u C-x =

-- Exercise. Define the _∨_ function:

_∨_ : Bool → Bool → Bool
_∨_ = {!!}

import Agdernoon.Exercise.Bool

------------------------------------------------------------------------
-- Natural numbers
------------------------------------------------------------------------

import Agdernoon.Data.Nat

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

pred : ℕ → ℕ
pred zero    = zero
pred (suc n) = n

infixl 7 _*_
infixl 6 _+_

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

-- Exercise. Define the _*_ function:

_*_ : ℕ → ℕ → ℕ
m * n = {!!}

import Agdernoon.Exercise.Nat

------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

infixr 5 _∷_

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A
