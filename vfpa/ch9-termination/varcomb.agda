module varcomb where

open import Data.String renaming (primStringEquality to strEq)
open import Data.Bool
open import Relation.Binary.PropositionalEquality hiding (subst)

infixl 6 _Ap_

data varcomb : Set where
  S : varcomb
  K : varcomb
  var : String → varcomb
  _Ap_ : varcomb → varcomb → varcomb

λ* : String → varcomb → varcomb
λ* _ S = K Ap S
λ* _ K = K Ap K
λ* s (x Ap y) = (S Ap (λ* s x)) Ap (S Ap (λ* s y))
λ* s (var v) = if strEq s v then S Ap K Ap K else K Ap (var v)

contains : String → varcomb → Bool
contains _ S = false
contains _ K = false
contains s (x Ap y) = contains s x ∨ contains s y
contains s (var v) = strEq s v

λ*-elim : ∀ (s : String) → (v : varcomb) → contains s (λ* s v) ≡ false
λ*-elim s S = refl
λ*-elim s K = refl
λ*-elim s (var x) with strEq s x | inspect (strEq s) x
... | true | [ eq ] = refl
... | false | [ eq ] rewrite eq = refl
λ*-elim s (x Ap y) rewrite λ*-elim s x | λ*-elim s y = refl

subst : varcomb → String → varcomb → varcomb
subst _ _ S = S
subst _ _ K = K
subst c s (var v) = if strEq s v then c else var v
subst c s (x Ap y) = subst c s x Ap subst c s y
