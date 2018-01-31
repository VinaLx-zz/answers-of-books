open import Level

module relation {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (_≥_ : A → A → Set ℓ₂) where

open import Data.Product

reflexive : Set (ℓ₁ ⊔ ℓ₂)
reflexive = ∀ {a : A} → a ≥ a

transitive : Set (ℓ₁ ⊔ ℓ₂)
transitive = ∀ {a b c : A} → a ≥ b → b ≥ c → a ≥ c

preorder : Set (ℓ₁ ⊔ ℓ₂)
preorder = reflexive × transitive
