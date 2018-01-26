module matrix-ex where

open import vec renaming (index to v-index)
open import Data.Nat

-- ex 5.1

𝕄 : ∀ {ℓ} → Set ℓ → ℕ → ℕ → Set ℓ
𝕄 A m n = 𝕍 (𝕍 A n) m

𝕄' : ℕ → ℕ → Set
𝕄' = 𝕄 ℕ

-- ex 5.2

𝕄-fill : ∀ {ℓ} {A : Set ℓ} {m n} → A → 𝕄 A m n
𝕄-fill {m = m} {n} a = repeat m (repeat n a)

𝕄-zero : ∀ {m n} → 𝕄' m n
𝕄-zero = 𝕄-fill 0

index : ∀ {ℓ} {A : Set ℓ} {m n} →
        (x : ℕ) → (y : ℕ) → 𝕄 A m n → {_ : x < m} → {_ : y < n} → A
index x y M = v-index y (v-index x M)

transpose : ∀ {ℓ} {A : Set ℓ} {m n} → 𝕄 A m n → 𝕄 A n m
transpose {n = n} [] = repeat n []
transpose (r :: v) = zipWith _::_ r (transpose v)
