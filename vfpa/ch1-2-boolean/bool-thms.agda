module bool-thms where

open import Agda.Builtin.Equality
open import bool

-- ~ ~ b ≡ b
~~-elim : ∀ b → ~ ~ b ≡ b
~~-elim t = refl
~~-elim f = refl

-- && idempotent
&&-idem : ∀ {b} → b && b ≡ b
&&-idem {t} = refl
&&-idem {f} = refl

-- || idempotent
||-idem : ∀ {b} -> b || b ≡ b
||-idem {t} = refl
||-idem {f} = refl

-- disjunct false
||-ff₁ : ∀ {x y} → x || y ≡ f → x ≡ f
||-ff₁ {f} p = refl
||-ff₁ {t} ()

||-ff₂ : ∀ {x y} → x || y ≡ f → y ≡ f
||-ff₂ {f}{f} p = refl
||-ff₂ {f}{t} ()
||-ff₂ {t} ()

-- conjunction true

&&-tt₁ : ∀ {x y} → x && y ≡ t → x ≡ t
&&-tt₁ {t} p = refl
&&-tt₁ {f} ()

&&-tt₂ : ∀ {x y} → x && y ≡ t → y ≡ t
&&-tt₂ {t}{t} p = refl
&&-tt₂ {t}{f} ()
&&-tt₂ {f} ()

--

same-branch : ∀ {ℓ}{A : Set ℓ} →
              ∀ (b : 𝔹) (a : A) →
              (if b then a else a) ≡ a
same-branch t a = refl
same-branch f a = refl

--

𝔹-contra : f ≡ t → ∀ {P} → P
𝔹-contra ()

--

xor-false : ∀ {x y} → x xor y ≡ f → x ≡ y
xor-false {t}{t} p = refl
xor-false {t}{f} ()
xor-false {f}{f} p = refl
xor-false {f}{t} ()
