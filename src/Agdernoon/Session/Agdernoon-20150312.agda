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

import Agdernoon.Data.List

infixr 5 _∷_ _++_

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

_++_ : ∀ {A} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

map : ∀ {A B} → (A → B) → List A → List B
map _ []       = []
map f (x ∷ xs) = f x ∷ map f xs

foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr _ n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

foldl : {A B : Set} → (A → B → A) → A → List B → A
foldl _ n []       = n
foldl c n (x ∷ xs) = foldl c (c n x) xs

-- Exercise. Define the filter function:

filter : ∀ {A} → (A → Bool) → List A → List A
filter = {!!}

-- import Agdernoon.Exercise.List

------------------------------------------------------------------------
-- Products
------------------------------------------------------------------------

import Agdernoon.Data.Product

infixr 4 _,_
infixr 2 _×_

data _×_ (A B : Set) : Set where
  _,_ : (x : A) (y : B) → A × B

proj₁ : ∀ {A B} → A × B → A
proj₁ (x , _) = x

proj₂ : ∀ {A B} → A × B → B
proj₂ (_ , y) = y

zip : ∀ {A B} → List A → List B → List (A × B)
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys
zip _        _        = []

partition : ∀ {A} → (A → Bool) → List A → List A × List A
partition _ []       = [] , []
partition p (x ∷ xs) with p x | partition p xs
... | false | ys , zs = ys , x ∷ zs
... | true  | ys , zs = x ∷ ys , zs

------------------------------------------------------------------------
-- Sums
------------------------------------------------------------------------

import Agdernoon.Data.Sum

infixr 1 _⊎_

data _⊎_ (A B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

-- Exercise. Define the [_,_] function:

[_,_] : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
[_,_] = {!!}

------------------------------------------------------------------------
-- Vectors
------------------------------------------------------------------------

import Agdernoon.Data.Vec

module Vector where

  infixr 5 _∷_

  data Vec (A : Set) : ℕ → Set where
    []  : Vec A zero
    _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

  head : ∀ {A n} → Vec A (suc n) → A
  head (x ∷ _) = x

  -- Exercise. Define the tail function:

  tail : ∀ {A n} → Vec A (suc n) → Vec A n
  tail xs = {!!}
