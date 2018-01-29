module printf where

open import Data.Char renaming (show to showChar)
open import Data.Nat
open import Data.Nat.Show renaming (show to showNat)
open import Data.List hiding (_++_)
open import Data.String hiding (show)
open import Function using (_∘_)

data format-d : Set where
  format-ℕ : format-d → format-d
  format-string : format-d → format-d
  not-format : Char → format-d → format-d
  empty-format : format-d

format-cover : List Char → format-d
format-cover ('%' ∷ 'n' ∷ s) = format-ℕ (format-cover s)
format-cover ('%' ∷ 's' ∷ s) = format-string (format-cover s)
format-cover (c ∷ s) = not-format c (format-cover s)
format-cover [] = empty-format

format-t' : format-d → Set
format-t' (format-ℕ v) = ℕ → format-t' v
format-t' (format-string v) = String → format-t' v
format-t' (not-format c v) = format-t' v
format-t' empty-format = String

format-t : String → Set
format-t = format-t' ∘ format-cover ∘ toList

format' : String → (d : format-d) → format-t' d
format' s (format-ℕ v) = λ n → format' (s ++ showNat n) v
format' s (format-string v) = λ s' → format' (s ++ s') v
format' s (not-format c v) = format' (s ++ showChar c) v
format' s empty-format = s

printf : (f : String) → format-t f
printf f = format' "" (format-cover (toList f))
