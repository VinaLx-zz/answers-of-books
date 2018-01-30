module termination where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Bool 
open import Data.Nat hiding (_⊔_)
open import Relation.Binary.PropositionalEquality
open import Data.Sum

data ↓ {ℓ₁ ℓ₂} {A : Set ℓ₁}
    (_>_ : A → A → Set ℓ₂) : A → Set (ℓ₁ ⊔ ℓ₂) where
    prf↓ : ∀ {x : A} → (∀ {y : A} → x > y → ↓ _>_ y) → ↓ _>_ x

↓Bool : ∀ {ℓ} {A : Set ℓ} (_>_ : A → A → Bool) → A → Set ℓ
↓Bool {ℓ} {A} _>_ = ↓{ℓ}{lzero} (λ (x y : A) → x > y ≡ true)

infix 5 _>ℕ_

_>ℕ_ : ℕ → ℕ → Bool
_>ℕ_ zero _ = false
_>ℕ_ (suc _) zero = true
_>ℕ_ (suc m) (suc n) = m >ℕ n

-- textbook implementation

>ℕ-split : ∀ {x y} → ((suc x) >ℕ y ≡ true) → x ≡ y ⊎ x >ℕ y ≡ true
>ℕ-split {zero} {zero} _ = inj₁ refl
>ℕ-split {zero} {suc y} prf = inj₂ prf
>ℕ-split {suc x} {zero} _ = inj₂ refl
>ℕ-split {suc x} {suc y} prf with >ℕ-split {x} {y} prf
... | inj₁ p rewrite p = inj₁ refl
... | inj₂ p = inj₂ p

>ℕ-↓ : ∀ (x : ℕ) → ↓Bool _>ℕ_ x
>ℕ-↓ x = prf↓ (h x)
    where h : ∀ x → ∀ {y} → x >ℕ y ≡ true → ↓Bool _>ℕ_ y
          h zero ()
          h (suc x) {y} p with >ℕ-split {x} {y} p
          ... | inj₁ prf rewrite sym prf = >ℕ-↓ x
          ... | inj₂ prf = h x {y} prf

↓measure : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set ℓ₁} {B : Set ℓ₂} →
           (_>A_ : A → A → Set ℓ₃) → (_>B_ : B → B → Set ℓ₄) →
           (f : A → B) → (∀ {x y : A} → x >A y → f x >B f y) →
           ∀ {a : A} → ↓ _>B_ (f a) → ↓ _>A_ a
↓measure {A = A} _>A_ _>B_ f mono {a} (prf↓ fb) = prf↓ h
    where h : {y : A} → a >A y → ↓ _>A_ y
          h {y} p = ↓measure _>A_ _>B_ f mono (fb (mono p))

