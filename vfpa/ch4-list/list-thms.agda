module list-thms where

open import list
open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool
open import Relation.Binary.PropositionalEquality

++-length : ∀ {ℓ} {A : Set ℓ} → (xs ys : 𝕃 A) →
            length xs + length ys ≡ length (xs ++ ys)
++-length [] ys = refl
++-length (x :: xs) ys rewrite ++-length xs ys = refl

++-assoc : ∀ {ℓ} {A : Set ℓ} → (xs ys zs : 𝕃 A) →
           xs ++ ys ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x :: xs) ys zs = refl

++-nil-id : ∀ {ℓ} {A : Set ℓ} → (xs : 𝕃 A) → (xs ++ []) ≡ xs
++-nil-id [] = refl
++-nil-id (x :: xs) rewrite ++-nil-id xs = refl

filter-length-mono : ∀ {ℓ} {A : Set ℓ} → (p : A → Bool) → (xs : 𝕃 A) →
                length (filter p xs) ≤ length xs
filter-length-mono p [] = z≤n
filter-length-mono p (x :: xs) with p x
... | true = s≤s (filter-length-mono p xs)
... | false = ≤⇒pred≤ (s≤s (filter-length-mono p xs))

-- implementation with Prelude
-- filter-length-mono p [] = diff zero refl
-- filter-length-mono p (x :: xs) with p x
-- filter-length-mono p (x :: xs) | true = suc-monotone (filter-length-mono p xs)
-- filter-length-mono p (x :: xs) | false = lt-right-mono (filter-length-mono p xs)
    -- where lt-right-mono : ∀ {m n : ℕ} → m < n → m < suc n
          -- lt-right-mono {m} {b} (diff d p) rewrite p = diff (suc d) refl

filter-idem : ∀ {ℓ} {A : Set ℓ} → (p : A → Bool) → (xs : 𝕃 A) →
              filter p (filter p xs) ≡ filter p xs
filter-idem p [] = refl
filter-idem p (x :: xs) with p x | inspect p x
... | true  | [ eq ] rewrite eq | eq | filter-idem p xs = refl
... | false | [ eq ] rewrite eq = filter-idem p xs

reverse'-length : ∀ {ℓ} {A : Set ℓ} → (xs ys : 𝕃 A) →
                length (reverse' xs ys) ≡ length xs + length ys
reverse'-length xs [] rewrite +-identityʳ (length xs) = refl
reverse'-length xs (y :: ys)
    -- length (reverse' (y :: xs) ys) ≡ length xs + suc (length ys)
    rewrite reverse'-length (y :: xs) ys
    -- suc (length xs + length ys) ≡ length xs + suc (length ys)
          | +-suc (length xs) (length ys) = refl

reverse-length : ∀ {ℓ} {A : Set ℓ} → (xs : 𝕃 A) →
                 length (reverse xs) ≡ length xs
reverse-length = reverse'-length []
