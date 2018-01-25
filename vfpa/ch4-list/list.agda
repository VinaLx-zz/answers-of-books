module list where

open import Data.Nat
open import Data.Bool

infixr 6 _::_ _++_

data 𝕃 {ℓ} (A : Set ℓ) : Set ℓ where
  [] : 𝕃 A
  _::_ : (x : A) (xs : 𝕃 A) → 𝕃 A


list = 𝕃

length : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → ℕ
length [] = zero
length (x :: xs) = suc (length xs)


_++_ : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → 𝕃 A → 𝕃 A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} →
      (A → B) → 𝕃 A → 𝕃 B
map f [] = []
map f (x :: xs) = f x :: map f xs

filter : ∀ {ℓ} {A : Set ℓ} → (A → Bool) → 𝕃 A → 𝕃 A
filter p [] = []
filter p (x :: xs) = if p x then x :: filter p xs else filter p xs

reverse' : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → 𝕃 A → 𝕃 A
reverse' acc [] = acc
reverse' acc (x :: xs) = reverse' (x :: acc) xs

reverse : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → 𝕃 A
reverse = reverse' []

take : ∀ {ℓ} {A : Set ℓ} → ℕ → 𝕃 A → 𝕃 A
take zero _ = []
take _ [] = []
take (suc n) (x :: xs) = x :: take n xs

repeat : ∀ {ℓ} {A : Set ℓ} → ℕ → A → 𝕃 A
repeat zero _ = []
repeat (suc n) a = a :: repeat n a

drop : ∀ {ℓ} {A : Set ℓ} → ℕ → 𝕃 A → 𝕃 A
drop zero xs = xs
drop _ [] = []
drop (suc n) (x :: xs) = drop n xs

takeWhile : ∀ {ℓ} {A : Set ℓ} → (A → Bool) → 𝕃 A → 𝕃 A
takeWhile p [] = []
takeWhile p (x :: xs) = if p x then x :: takeWhile p xs else []

