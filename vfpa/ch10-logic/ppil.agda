-- PPIL : Positive Propositional Intuitionistic Logic

module ppil where

open import Data.String renaming (primStringEquality to strEq)
open import Data.List
open import Data.Product
open import Data.Unit hiding (preorder)
open import relation

infixr 6 _⇒_
infixl 7 _∧_

data Formula : Set where
  $ : String → Formula
  True : Formula
  _∧_  : Formula → Formula → Formula
  _⇒_  : Formula → Formula → Formula

Context : Set
Context = List Formula

infix 5 _⊢_

data _⊢_ : Context → Formula → Set where
  True-intro : ∀ {Γ} → Γ ⊢ True
  assume  : ∀ {Γ f} → (f ∷ Γ) ⊢ f
  weaken  : ∀ {Γ f₁ f₂} → Γ ⊢ f₁ → (f₂ ∷ Γ) ⊢ f₁
  ⇒-intro : ∀ {Γ f₁ f₂} → (f₁ ∷ Γ) ⊢ f₂ → Γ ⊢ f₁ ⇒ f₂
  ⇒-elim  : ∀ {Γ f₁ f₂} → Γ ⊢ f₁ ⇒ f₂ → Γ ⊢ f₁ → Γ ⊢ f₂
  ∧-intro : ∀ {Γ f₁ f₂} → Γ ⊢ f₁ → Γ ⊢ f₂ → Γ ⊢ f₁ ∧ f₂
  ∧-elim1 : ∀ {Γ f₁ f₂} → Γ ⊢ f₁ ∧ f₂ → Γ ⊢ f₁
  ∧-elim2 : ∀ {Γ f₁ f₂} → Γ ⊢ f₁ ∧ f₂ → Γ ⊢ f₂

record Kripke : Set1 where
  field
    W : Set
    R : W → W → Set
    R-preorder : preorder R
    V : W → String → Set
    V-mono : ∀ {w₁ w₂} → R w₁ w₂ → ∀ {i} → V w₁ i → V w₂ i

R-refl : ∀ {k : Kripke} → reflexive (Kripke.R k)
R-refl {k} = proj₁ R-preorder where open Kripke k

R-trans : ∀ {k : Kripke} → transitive (Kripke.R k)
R-trans {k} = proj₂ R-preorder where open Kripke k

_,_⊨_ : ∀ (k : Kripke) → Kripke.W k → Formula → Set
k , w ⊨ $ x  = Kripke.V k w x
k , w ⊨ True = ⊤
k , w ⊨ (f₁ ∧ f₂) = (k , w ⊨ f₁) × (k , w ⊨ f₂)
k , w ⊨ (f₁ ⇒ f₂) = ∀ {w' : Kripke.W k} → Kripke.R k w w' →
                    k , w' ⊨ f₁ → k , w' ⊨ f₂

_,_⊨ctx_ : ∀ (k : Kripke) → Kripke.W k → Context → Set
k , w ⊨ctx [] = ⊤
k , w ⊨ctx (x ∷ context) = (k , w ⊨ x) × (k , w ⊨ctx context)

⊨-mono : ∀ {k : Kripke} {w₁ w₂ : Kripke.W k} {f : Formula} →
         Kripke.R k w₁ w₂ → k , w₁ ⊨ f → k , w₂ ⊨ f
⊨-mono {k} {f = $ x} r p = Kripke.V-mono k r p
⊨-mono {f = True} _ _ = tt
⊨-mono {k} {f = f₁ ∧ f₂} r (p₁ , p₂) = ⊨-mono {f = f₁} r p₁ , ⊨-mono {f = f₂} r p₂ -- ⊨-mono r p₁ , ⊨-mono r p₂
⊨-mono {k} {f = f₁ ⇒ f₂} r p = λ r' → p (R-trans {k} r r')


⊨ctx-mono : ∀ {k : Kripke} {Γ : Context} {w₁ w₂ : Kripke.W k} →
            Kripke.R k w₁ w₂ → k , w₁ ⊨ctx Γ → k , w₂ ⊨ctx Γ
⊨ctx-mono {k} {[]} _ _ = tt
⊨ctx-mono {k} {f ∷ Γ} r (px , pxs) = ⊨-mono {f = f} r px , ⊨ctx-mono {Γ = Γ} r pxs

_⊩_ : Context → Formula → Set1
Γ ⊩ f = ∀ {k : Kripke} {w : Kripke.W k} → k , w ⊨ctx Γ → k , w ⊨ f

soundness : ∀ {Γ : Context} {f : Formula} → Γ ⊢ f → Γ ⊩ f
-- soundness : ∀ {Γ : Context} {f : Formula} → Γ ⊢ f →
--             ∀ {k : Kripke} {w : Kripke W. k} → (k , w ⊨ctx Γ) → (k , w ⊨ f)

soundness True-intro     _    = tt
soundness assume         cprf = proj₁ cprf
soundness (weaken p)     cprf = soundness p (proj₂ cprf)
soundness (⇒-intro {Γ} {f₁} {f₂} p) cprf r f₁p = soundness p (f₁p , ⊨ctx-mono r cprf)
soundness (⇒-elim p₁ p₂) {k} cprf = soundness p₁ cprf (R-refl {k}) (soundness p₂ cprf)
soundness (∧-intro p p₁) cprf = soundness p cprf , soundness p₁ cprf
soundness (∧-elim1 p)    cprf = proj₁ (soundness p cprf)
soundness (∧-elim2 p)    cprf = proj₂ (soundness p cprf)

infix 4 _≼_

data _≼_ : Context → Context → Set where
  ≼-refl : ∀ {Γ} → Γ ≼ Γ
  ≼-cons : ∀ {Γ Γ' f} → Γ ≼ Γ' → Γ ≼ f ∷ Γ'

≼-trans : transitive _≼_
≼-trans ab ≼-refl = ab
≼-trans ab (≼-cons bc) = ≼-cons (≼-trans ab bc)

≼-weaken : ∀ {Γ Γ'} {f : Formula} → Γ ≼ Γ' → Γ ⊢ f → Γ' ⊢ f
≼-weaken ≼-refl f = f
≼-weaken (≼-cons x) f = weaken (≼-weaken x f)

U : Kripke
U = record
    { W = Context
    ; R = _≼_
    ; R-preorder = ≼-refl , ≼-trans
    ; V = λ Γ v → Γ ⊢ $ v
    ; V-mono = λ r v → ≼-weaken r v }

u-completeness : ∀ {f : Formula} {Γ : Context} → U , Γ ⊨ f → Γ ⊢ f
u-soundness : ∀ {f : Formula} {Γ : Context} → Γ ⊢ f → U , Γ ⊨ f

u-completeness {$ x} v = v
u-completeness {True} _ = True-intro
u-completeness {f₁ ∧ f₂} (p₁ , p₂) = ∧-intro (u-completeness p₁) (u-completeness p₂)
u-completeness {f₁ ⇒ f₂} p = ⇒-intro
    (u-completeness {f = f₂}
        (p (≼-cons ≼-refl) (u-soundness {f = f₁} assume)))

u-soundness {$ x} p = p
u-soundness {True} p = tt
u-soundness {f₁ ∧ f₂} p = u-soundness (∧-elim1 p) , u-soundness (∧-elim2 p)
u-soundness {f₁ ⇒ f₂} p r p₁ =
    u-soundness (⇒-elim (≼-weaken r p) (u-completeness p₁))

context-id : ∀ {Γ : Context} → U , Γ ⊨ctx Γ
context-id {[]} = tt
context-id {f ∷ Γ} = u-soundness {f} assume
                   , ⊨ctx-mono (≼-cons ≼-refl) (context-id {Γ})

completeness : ∀ {Γ : Context} {f : Formula} → Γ ⊩ f → Γ ⊢ f
completeness {Γ} {f} p =
    u-completeness {f} {Γ} (p {U} {Γ} (context-id {Γ}))

nbe : ∀ {Γ f} → Γ ⊢ f → Γ ⊢ f
nbe p = completeness (soundness p)

