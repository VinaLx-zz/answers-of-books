module list-thms-ex where

open import Data.Nat
open import Data.Bool
open import list
open import list-thms using (++-nil-id)
open import Relation.Binary.PropositionalEquality

filter-repeat-nil : ∀ {ℓ} {A : Set ℓ} {p : A → Bool} {a : A} {n : ℕ} →
                    p a ≡ false → filter p (repeat n a) ≡ []
filter-repeat-nil {p = p} {a} {zero} prf = refl
filter-repeat-nil {p = p} {a} {suc n} prf
    rewrite prf
          | filter-repeat-nil {p = p} {a} {n} prf = refl

filter-++-distr : ∀ {ℓ} {A : Set ℓ} {p : A → Bool} {xs ys : 𝕃 A} →
                  filter p (xs ++ ys) ≡ filter p xs ++ filter p ys
filter-++-distr {p = p} {[]} {ys} = refl
filter-++-distr {p = p} {x :: xs} {ys}
    rewrite filter-++-distr {p = p} {xs} {ys} with p x 
... | true = refl
... | false = refl

takeWhile-repeat : ∀ {ℓ} {A : Set ℓ} {p : A → Bool} {a : A} {n : ℕ} →
                   p a ≡ true → takeWhile p (repeat n a) ≡ repeat n a
takeWhile-repeat {p = p} {a} {zero} prf = refl
takeWhile-repeat {p = p} {a} {suc n} prf
    rewrite prf | takeWhile-repeat {p = p} {a} {n} prf = refl

take-drop : ∀ {ℓ} {A : Set ℓ} → (n : ℕ) → (xs : 𝕃 A) →
            take n xs ++ drop n xs ≡ xs
take-drop zero xs = refl
take-drop (suc n) [] = refl
take-drop (suc n) (x :: xs) rewrite take-drop n xs = refl
