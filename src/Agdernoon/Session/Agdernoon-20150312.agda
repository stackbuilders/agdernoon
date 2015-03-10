------------------------------------------------------------------------
-- The Agdernoon sessions
--
-- 1 (2015/03/12)
------------------------------------------------------------------------

module Agdernoon.Session.Agdernoon-20150312 where

------------------------------------------------------------------------
-- Agda
------------------------------------------------------------------------

-- Agda is a dependently typed functional programming language.

-- Agda is a proof assistant.

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

-- Some key bindings

-- C-c C-a         auto
-- C-c C-b         previous goal
-- C-c C-c         make case
-- C-c C-d         infer type maybe toplevel
-- C-c C-e         show context
-- C-c C-f         next goal
-- C-c C-h         helper function type
-- C-c C-l         load
-- C-c C-n         compute normalise value maybe toplevel
-- C-c C-r         refine
-- C-c C-t         goal type
-- C-c C-w         why in scope maybe toplevel

-- C-u C-x =       α β γ δ ε ζ η θ ι κ λ μ ν ξ ο π ρ σ τ υ φ χ ψ ω

-- C-c C-x C-d     remove annotations
-- C-c C-x C-q     quit
-- C-c C-x C-r     restart

-- M-*             go back
-- M-.             go to definition

-- Exercise. Define the _∨_ function:

_∨_ : Bool → Bool → Bool
_∨_ = {!!}

import Agdernoon.Exercise.Bool

infix  0 if_then_else

if_then_else : {A : Set} → Bool → A → A → A
if false then _ else f = f
if true  then t else _ = t

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
-- System T (Bove and Dybjer 2009, § 2.5)
------------------------------------------------------------------------

natrec : {C : Set} → C → (ℕ → C → C) → ℕ → C
natrec p h zero    = p
natrec p h (suc n) = h n (natrec p h n)

plus : ℕ → ℕ → ℕ
plus n m = natrec m (λ x y → suc y) n

mult : ℕ → ℕ → ℕ
mult n m = natrec zero (λ x y → plus y m) n

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

  vmap : ∀ {A B n} → (A → B) → Vec A n → Vec B n
  vmap _ []       = []
  vmap f (x ∷ xs) = f x ∷ vmap f xs

  -- (Norell 2009, p. 236)

  data Vec₂ (A : Set) : ℕ → Set where
    nil  : Vec₂ A zero
    cons : (n : ℕ) → A → Vec₂ A n → Vec₂ A (suc n)

  vmap₂ : ∀ {A B} (n : ℕ) → (A → B) → Vec₂ A n → Vec₂ B n
  vmap₂ .zero    _ nil           = nil
  vmap₂ .(suc n) f (cons n x xs) = cons n (f x) (vmap₂ n f xs)

  vmap₃ : ∀ {A B} (n : ℕ) → (A → B) → Vec₂ A n → Vec₂ B n
  vmap₃ zero    _ nil            = nil
  vmap₃ (suc n) f (cons .n x xs) = cons n (f x) (vmap₃ n f xs)
