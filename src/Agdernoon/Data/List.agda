------------------------------------------------------------------------
-- The Agdernoon library
--
-- Lists
------------------------------------------------------------------------

module Agdernoon.Data.List where

open import Agdernoon.Data.Bool
open import Agdernoon.Data.Nat
open import Agdernoon.Data.Product

infixr 5 _∷_ _++_

------------------------------------------------------------------------
--

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

------------------------------------------------------------------------
-- Some operations

-- * Basic functions

[_] : ∀ {A} → A → List A
[ x ] = x ∷ []

_++_ : ∀ {A} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

null : ∀ {A} → List A → Bool
null []      = true
null (_ ∷ _) = false

-- * List transformations

map : ∀ {A B} → (A → B) → List A → List B
map _ []       = []
map f (x ∷ xs) = f x ∷ map f xs

replicate : ∀ {A} (n : ℕ) → A → List A
replicate zero    _ = []
replicate (suc n) x = x ∷ replicate n x

zipWith : ∀ {A B C} → (A → B → C) → List A → List B → List C
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys
zipWith f _        _        = []

zip : ∀ {A B} → List A → List B → List (A × B)
zip = zipWith _,_

intersperse : ∀ {A} → A → List A → List A
intersperse _ []           = []
intersperse _ (y ∷ [])     = [ y ]
intersperse x (y ∷ z ∷ zs) = y ∷ x ∷ intersperse x (z ∷ zs)

-- * Reducing lists (folds)

foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr _ n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

foldl : {A B : Set} → (A → B → A) → A → List B → A
foldl _ n []       = n
foldl c n (x ∷ xs) = foldl c (c n x) xs

-- * Searching lists

filter : ∀ {A} → (A → Bool) → List A → List A
filter _ []       = []
filter p (x ∷ xs) with p x
... | true  = x ∷ filter p xs
... | false =     filter p xs
