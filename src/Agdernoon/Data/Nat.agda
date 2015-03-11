------------------------------------------------------------------------
-- The Agdernoon library
--
-- Natural numbers
------------------------------------------------------------------------

module Agdernoon.Data.Nat where

open import Agdernoon.Function

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

------------------------------------------------------------------------
--

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

import Data.Nat

fold : {A : Set} → A → (A → A) → ℕ → A
fold z _ zero    = z
fold z s (suc n) = s (fold z s n)

pred : ℕ → ℕ
pred zero    = zero
pred (suc n) = n

infixl 7 _*_
infixl 6 _+_

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero  * _ = zero
suc m * n = n + m * n
