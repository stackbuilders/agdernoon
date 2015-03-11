------------------------------------------------------------------------
-- The Agdernoon library
--
-- Some properties about natural number operations
------------------------------------------------------------------------

module Agdernoon.Data.Nat.Properties where

open import Agdernoon.Data.Nat

open import Relation.Binary.PropositionalEquality

open Relation.Binary.PropositionalEquality.≡-Reasoning

+-assoc : ∀ m n o → (m + n) + o ≡ m + (n + o)
+-assoc zero    _ _ = refl
+-assoc (suc m) n o = cong suc (+-assoc m n o)

+-right-identity : ∀ n → n + zero ≡ n
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

*-right-zero : ∀ n → n * zero ≡ zero
*-right-zero zero    = refl
*-right-zero (suc n) = *-right-zero n

*-comm : ∀ m n → m * n ≡ n * m
*-comm zero    n = sym (*-right-zero n)
*-comm (suc m) n =
  begin
    suc m * n
  ≡⟨ refl ⟩
    n + m * n
  ≡⟨ cong (λ x → n + x) (*-comm m n) ⟩
    n + n * m
  ≡⟨ sym (+-*-suc n m) ⟩
    n * suc m
  ∎
