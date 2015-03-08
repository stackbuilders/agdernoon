------------------------------------------------------------------------
-- The Agdernoon library
--
--
------------------------------------------------------------------------

module Agdernoon.Data.List.Properties where

open import Agdernoon.Data.List
open import Agdernoon.Data.Product
open import Agdernoon.Function

open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
--

∷-injective : ∀ {A} {x y : A} {xs ys} →
              x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
∷-injective refl = refl , refl

right-identity-unique : ∀ {A} (xs : List A) {ys} →
                        xs ≡ xs ++ ys → ys ≡ []
right-identity-unique []       refl = refl
right-identity-unique (x ∷ xs) eq   =
  right-identity-unique xs (proj₂ (∷-injective eq))



map-++-commute : ∀ {A B} (f : A → B) xs ys →
                 map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute _ []       _  = refl
map-++-commute f (x ∷ xs) ys = cong (_∷_ (f x)) (map-++-commute f xs ys)

map-id : ∀ {A} (xs : List A) → map id xs ≡ xs
map-id []       = refl
map-id (x ∷ xs) = cong (_∷_ x) (map-id xs)

map-∘ : ∀ {A B C} {g : B → C} {f : A → B} (xs : List A) →
        map (g ∘ f) xs ≡ map g (map f xs)
map-∘             []       = refl
map-∘ {g = g} {f} (x ∷ xs) = cong (_∷_ (g (f x))) (map-∘ xs)
