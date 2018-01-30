module combinator where

open import Data.Nat
open import Data.String renaming (primStringEquality to strEq)

infixl 6 _Ap_

data comb : Set where
  S : comb
  K : comb
  _Ap_ : comb → comb → comb

infix 5 _⇝_

data _⇝_ : comb → comb → Set where
  ⇝K : (a : comb) → (b : comb) → K Ap a Ap b ⇝ a
  ⇝S : (a : comb) → (b : comb) → (c : comb) → S Ap a Ap b Ap c ⇝ (a Ap c) Ap (b Ap c)
  ⇝Cong1 : {a₁ a₂ : comb} → (b : comb) → a₁ ⇝ a₂ → a₁ Ap b ⇝ a₂ Ap b
  ⇝Cong2 : (a : comb) → {b₁ b₂ : comb} → b₁ ⇝ b₂ → a Ap b₁ ⇝ a Ap b₂


