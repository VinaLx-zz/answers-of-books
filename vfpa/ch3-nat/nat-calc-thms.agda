module nat-calc-thms where

open import nat
open import Prelude.Equality

---- addition ----

-- identity

id-0+ : ∀ (n : ℕ) → z + n ≡ n
id-0+ n = refl

id-+0 : ∀ (n : ℕ) → n + z ≡ n
id-+0 z = refl
id-+0 (s n) rewrite id-+0 n = refl

-- associativity

+-assoc : ∀ (a b c : ℕ) → a + (b + c) ≡ (a + b) + c
+-assoc z b c = refl
+-assoc (s a) b c rewrite +-assoc a b c = refl

-- commutativity

eq-+s : ∀ (a b : ℕ) → a + (s b) ≡ s (a + b)
eq-+s z b = refl
eq-+s (s a) b rewrite eq-+s a b = refl

+-commute : ∀ (a b : ℕ) → a + b ≡ b + a
+-commute z b rewrite id-+0 b = refl
+-commute (s a) b            -- s (a + b) ≡ b + s a
    rewrite +-commute a b    -- s (b + a) ≡ b + s a
          | eq-+s b a = refl


---- multiplication ----

-- null

null-0* : ∀ (n : ℕ) → z * n ≡ z
null-0* n = refl

null-*0 : ∀ (n : ℕ) → n * z ≡ z
null-*0 z = refl
null-*0 (s n) rewrite null-*0 n = refl

-- identity

id-1* : ∀ (n : ℕ) → (s z) * n ≡ n
id-1* n rewrite id-+0 n = refl

id-*1 : ∀ (n : ℕ) → n * (s z) ≡ n
id-*1 z = refl
id-*1 (s n) rewrite id-*1 n = refl

-- distributivity

*-distr : ∀ (a b c : ℕ) → (a + b) * c ≡ a * c + b * c
*-distr z b c = refl
*-distr (s a) b c               -- c + (a + b) * c ≡ c + a * c + b * c
    rewrite *-distr a b c       -- c + (a * c + b * c) ≡ c + a * c + b * c
    = +-assoc c (a * c) (b * c)

-- associativity

*-assoc : ∀ (a b c : ℕ) → a * (b * c) ≡ (a * b) * c
*-assoc z b c = refl
*-assoc (s a) b c rewrite *-assoc a b c | *-distr b (a * b) c = refl

-- commutativity

eq-*s : ∀ (a b : ℕ) → a + a * b ≡ a * (s b)
eq-*s z b = refl
eq-*s (s a) b                   -- s (a + (b + a * b)) ≡ s (b + a * s b)
    rewrite +-assoc a b (a * b) -- s (a + b + a * b) ≡ s (b + a * s b)
          | +-commute a b       -- s (b + a + a * b) ≡ s (b + a + s b)
          | sym (eq-*s a b)     -- s (b + a + a * b) ≡ s (b + (a + a * b))
          | +-assoc b a (a * b) = refl


*-commute : ∀ (a b : ℕ) → a * b ≡ b * a
*-commute z b rewrite null-*0 b = refl
*-commute (s a) b rewrite *-commute a b = eq-*s b a

