------------------------------------------------------------------------
-- The Agdernoon exercises
--
-- Natural numbers
------------------------------------------------------------------------

module Agdernoon.Exercise.Nat where

open import Agdernoon.Data.Nat hiding (_*_)

infixl 7 _*_

------------------------------------------------------------------------
-- Exercise. Define the _*_ function:

_*_ : ℕ → ℕ → ℕ
zero  * _ = zero
suc m * n = n + m * n
