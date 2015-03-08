------------------------------------------------------------------------
-- The Agdernoon library
--
-- The Maybe type
------------------------------------------------------------------------

module Agdernoon.Data.Maybe where

open import Agdernoon.Data.Bool
open import Agdernoon.Function

------------------------------------------------------------------------
-- The type

data Maybe (A : Set) : Set where
  just    : (x : A) → Maybe A
  nothing : Maybe A

------------------------------------------------------------------------
-- Some operations

is-just : ∀ {A} → Maybe A → Bool
is-just (just _) = true
is-just nothing  = false

is-nothing : ∀ {A} → Maybe A → Bool
is-nothing = not ∘ is-just

maybe : {A B : Set} → (A → B) → B → Maybe A → B
maybe j _ (just x) = j x
maybe _ n nothing  = n
