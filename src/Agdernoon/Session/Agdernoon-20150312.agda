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

-- http://wiki.portal.chalmers.se/agda/pmwiki.php

------------------------------------------------------------------------
-- Booleans
------------------------------------------------------------------------

import Agdernoon.Data.Bool
import Agdernoon.Exercise.Bool

module Bool where

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
  -- C-c C-d         infer type
  -- C-c C-e         show context
  -- C-c C-f         next goal
  -- C-c C-h         helper function type
  -- C-c C-l         load
  -- C-c C-n         compute normalise value
  -- C-c C-r         refine
  -- C-c C-t         goal type
  -- C-c C-w         why in scope

  -- C-u C-x =       how to input
  --                 α β γ δ ε ζ η θ ι κ λ μ ν ξ ο π ρ σ τ υ φ χ ψ ω

  -- C-c C-x C-d     remove annotations
  -- C-c C-x C-q     quit
  -- C-c C-x C-r     restart

  -- M-*             go back
  -- M-.             go to definition

  -- Exercise. Define the _∨_ function:

  _∨_ : Bool → Bool → Bool
  _∨_ = {!!}

  infix  0 if_then_else

  if_then_else : {A : Set} → Bool → A → A → A
  if false then _ else f = f
  if true  then t else _ = t

------------------------------------------------------------------------
-- Natural numbers
------------------------------------------------------------------------

import Agdernoon.Data.Nat
import Agdernoon.Exercise.Nat

module Nat where

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

  open Bool

  mutual

    even : ℕ → Bool
    even zero    = true
    even (suc n) = odd n

    odd : ℕ → Bool
    odd zero    = false
    odd (suc n) = even n

even-zero = Nat.even Nat.zero
even-one  = Nat.even (Nat.suc Nat.zero)

odd-zero = Nat.odd Nat.zero
odd-one  = Nat.odd (Nat.suc Nat.zero)

------------------------------------------------------------------------
-- System T (Bove and Dybjer 2009, § 2.5)
------------------------------------------------------------------------

module SystemT where

  open Nat

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
import Agdernoon.Exercise.List

module List where

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

  open Bool

  filter : ∀ {A} → (A → Bool) → List A → List A
  filter = {!!}

------------------------------------------------------------------------
-- Products
------------------------------------------------------------------------

import Agdernoon.Data.Product

module Product where

  infixr 4 _,_
  infixr 2 _×_

  data _×_ (A B : Set) : Set where
    _,_ : (x : A) (y : B) → A × B

  proj₁ : ∀ {A B} → A × B → A
  proj₁ (x , _) = x

  proj₂ : ∀ {A B} → A × B → B
  proj₂ (_ , y) = y

  open List

  zip : ∀ {A B} → List A → List B → List (A × B)
  zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys
  zip _        _        = []

  open Bool

  partition : ∀ {A} → (A → Bool) → List A → List A × List A
  partition _ []       = [] , []
  partition p (x ∷ xs) with p x | partition p xs
  ... | false | ys , zs = ys , x ∷ zs
  ... | true  | ys , zs = x ∷ ys , zs

------------------------------------------------------------------------
-- Sums
------------------------------------------------------------------------

import Agdernoon.Data.Sum
import Agdernoon.Exercise.Sum

module Sum where

  infixr 1 _⊎_

  data _⊎_ (A B : Set) : Set where
    inj₁ : (x : A) → A ⊎ B
    inj₂ : (y : B) → A ⊎ B

  -- Exercise. Define the [_,_] function:

  [_,_] : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
  [_,_] = {!!}

------------------------------------------------------------------------
-- Identity
------------------------------------------------------------------------

module Identity where

  id₂ : (A : Set) → A → A
  id₂ _ x = x

  open Nat

  idℕ = id₂ ℕ

  id : {A : Set} → A → A
  id x = x

------------------------------------------------------------------------
-- Vectors
------------------------------------------------------------------------

import Agdernoon.Data.Vec
import Agdernoon.Exercise.Vec

module Vec where

  open Nat

  infixr 5 _∷_

  data Vec (A : Set) : ℕ → Set where
    []  : Vec A zero
    _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

  head : ∀ {A n} → Vec A (suc n) → A
  head (x ∷ _) = x

  -- Exercise. Define the tail function:

  tail : ∀ {A n} → Vec A (suc n) → Vec A n
  tail xs = {!!}

  map : ∀ {A B n} → (A → B) → Vec A n → Vec B n
  map _ []       = []
  map f (x ∷ xs) = f x ∷ map f xs

  -- (Norell 2009, p. 236)

  data Vec₂ (A : Set) : ℕ → Set where
    nil  : Vec₂ A zero
    cons : (n : ℕ) → A → Vec₂ A n → Vec₂ A (suc n)

  map₂ : ∀ {A B} (n : ℕ) → (A → B) → Vec₂ A n → Vec₂ B n
  map₂ .zero    _ nil           = nil
  map₂ .(suc n) f (cons n x xs) = cons n (f x) (map₂ n f xs)

  map₃ : ∀ {A B} (n : ℕ) → (A → B) → Vec₂ A n → Vec₂ B n
  map₃ zero    _ nil            = nil
  map₃ (suc n) f (cons .n x xs) = cons n (f x) (map₃ n f xs)

------------------------------------------------------------------------
-- (Norell 2009, § 2.6)
------------------------------------------------------------------------

import Agdernoon.Data.List
-- import Agdernoon.Exercise.Sublist

module Sublist where

  open import Agdernoon.Data.Bool
  open import Agdernoon.Data.List using (List; []; _∷_; filter)

  open Nat

  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  data _≢_ : ℕ → ℕ → Set where
    z≢s : ∀ {n} → zero ≢ suc n
    s≢z : ∀ {n} → suc n ≢ zero
    s≢s : ∀ {m n} → m ≢ n → suc m ≢ suc n

  data Equal? (m n : ℕ) : Set where
    eq  : m ≡ n → Equal? m n
    neq : m ≢ n → Equal? m n

  equal? : (m n : ℕ) → Equal? m n
  equal? zero    zero    = eq refl
  equal? zero    (suc n) = neq z≢s
  equal? (suc m) zero    = neq s≢z
  equal? (suc m) (suc n) with equal? m n
  equal? (suc m) (suc .m) | eq refl = eq refl
  equal? (suc m) (suc n)  | neq m≢n = neq (s≢s m≢n)

  infix  4 _⊆_

  data _⊆_ {A : Set} : List A → List A → Set where
    stop : [] ⊆ []
    drop : ∀ {x xs ys} → xs ⊆ ys → xs ⊆ x ∷ ys
    keep : ∀ {x xs ys} → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys

  lem-filter : ∀ {A} (p : A → Bool) (xs : List A) → filter p xs ⊆ xs
  lem-filter p []       = stop
  lem-filter p (x ∷ xs) with p x
  ... | true  = keep (lem-filter p xs)
  ... | false = drop (lem-filter p xs)

  lem-plus-zero : (n : ℕ) → n + zero ≡ n
  lem-plus-zero zero    = refl
  lem-plus-zero (suc n) with n + zero | lem-plus-zero n
  ... | .n | refl = refl

  -- Exercise. Prove the reflexivity of _⊆_:

  ⊆-refl : ∀ {A} {xs : List A} → xs ⊆ xs
  ⊆-refl {xs = xs} = {!!}

  -- Exercise. Prove the transitivity of _⊆_:

  ⊆-trans : ∀ {A} {xs ys zs : List A} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
  ⊆-trans xs⊆ys ys⊆zs = {!!}

------------------------------------------------------------------------
-- Propositions as types (Sicard-Ramírez 2011)
------------------------------------------------------------------------

module PropositionsAsTypes where

  ----------------------------------------------------------------------
  -- Propositional logic

  -- Conjunction: Product

  infixr 6 _,_
  infixr 5 _∧_

  data _∧_ (A B : Set) : Set where
    _,_ : A → B → A ∧ B

  ∧-proj₁ : ∀ {A B} → A ∧ B → A
  ∧-proj₁ (a , b) = a

  ∧-proj₂ : ∀ {A B} → A ∧ B → B
  ∧-proj₂ (a , b) = b

  -- Disjunction: Sum

  infixr 4 _∨_

  data _∨_ (A B : Set) : Set where
    inj₁ : A → A ∨ B
    inj₂ : B → A ∨ B

  [_,_] : {A B C : Set} → (A → C) → (B → C) → A ∨ B → C
  [_,_] f g (inj₁ a) = f a
  [_,_] f g (inj₂ b) = g b

  -- False: Empty

  data ⊥ : Set where

  ⊥-elim : {A : Set} → ⊥ → A
  ⊥-elim ()

  -- True: Unit

  data ⊤ : Set where
    tt : ⊤

  -- Implication

  data _↝_ (A B : Set) : Set where
    fun : (A → B) → A ↝ B

  apply : ∀ {A B} → A → (A ↝ B) → B
  apply a (fun f) = f a

  -- Negation

  infix  6 ¬_

  ¬_ : Set → Set
  ¬ A = A → ⊥

  infixr 2 _↔_

  _↔_ : Set → Set → Set
  A ↔ B = A → B ∧ B → A

  a→¬¬a : ∀ {A} → A → ¬ ¬ A
  a→¬¬a a ¬a = ¬a a

  ----------------------------------------------------------------------
  -- Predicate logic

  -- Existential quantifier

  data ∃ (A : Set) (B : A → Set) : Set where
    _,_ : (witness : A) → B witness → ∃ A B

  ∃-proj₁ : ∀ {A B} → ∃ A B → A
  ∃-proj₁ (witness , _) = witness

  ∃-proj₂ : ∀ {A B} (p : ∃ A B) → B (∃-proj₁ p)
  ∃-proj₂ (witness , x) = x

  -- Universal quantifier

  data Forall (A : Set) (B : A → Set) : Set where
    dfun : ((a : A) → B a) → Forall A B

  dapply : ∀ {A B} → Forall A B → (a : A) → B a
  dapply (dfun f) a = f a

  ----------------------------------------------------------------------
  -- Equality

  data _≡_ {A : Set} : A → A → Set where
    refl : (a : A) → a ≡ a

------------------------------------------------------------------------
-- Equational reasoning
------------------------------------------------------------------------

import Data.Nat.Properties.Simple

module EquationalReasoning where

  open import Data.List
  open import Data.Nat
  open import Relation.Binary.PropositionalEquality

  open Relation.Binary.PropositionalEquality.≡-Reasoning

  +-assoc : ∀ m n o → (m + n) + o ≡ m + (n + o)
  +-assoc zero    _ _ = refl
  +-assoc (suc m) n o = cong suc (+-assoc m n o)

  +-right-identity : ∀ n → n + 0 ≡ n
  +-right-identity zero    = refl
  +-right-identity (suc n) = cong suc (+-right-identity n)

  +-suc : ∀ m n → m + suc n ≡ suc (m + n)
  +-suc zero    _ = refl
  +-suc (suc m) n = cong suc (+-suc m n)

  +-comm : ∀ m n → m + n ≡ n + m
  +-comm zero    n = sym (+-right-identity n)
  +-comm (suc m) n =
    begin
      suc m + n
    ≡⟨ refl ⟩
      suc (m + n)
    ≡⟨ cong suc (+-comm m n) ⟩
      suc (n + m)
    ≡⟨ sym (+-suc n m) ⟩
      n + suc m
    ∎

  +-*-suc : ∀ m n → m * suc n ≡ m + m * n
  +-*-suc zero    _ = refl
  +-*-suc (suc m) n =
    begin
      suc m * suc n
    ≡⟨ refl ⟩
      suc n + m * suc n
    ≡⟨ cong (λ x → suc n + x) (+-*-suc m n) ⟩
      suc n + (m + m * n)
    ≡⟨ refl ⟩
      suc (n + (m + m * n))
    ≡⟨ cong suc (sym (+-assoc n m (m * n))) ⟩
      suc (n + m + m * n)
    ≡⟨ cong (λ x → suc (x + m * n)) (+-comm n m) ⟩
      suc (m + n + m * n)
    ≡⟨ cong suc (+-assoc m n (m * n)) ⟩
      suc (m + (n + m * n))
    ≡⟨ refl ⟩
      suc m + suc m * n
    ∎

  *-right-zero : ∀ n → n * 0 ≡ 0
  *-right-zero zero    = refl
  *-right-zero (suc n) = *-right-zero n

  -- Exercise. Prove the commutativity of _*_:

  *-comm : ∀ m n → m * n ≡ n * m
  *-comm m n = {!!}
