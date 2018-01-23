module nat where

open import Prelude.Bool

data ℕ : Set where
  z : ℕ
  s : ℕ → ℕ

infixl 10 _*_
infixl 9 _+_ _-_
infixl 8 _==_ _<_ _>_

_+_ : ℕ → ℕ → ℕ
z + n = n
(s m) + n = s (m + n)

_-_ : ℕ → ℕ → ℕ
z - n = z
n - z = n
(s m) - (s n) = m - n

_*_ : ℕ → ℕ → ℕ
z * n = z
(s m) * n = n + m * n

_==_ : ℕ → ℕ → Bool
z == z = true
z == (s n) = false
(s m) == z = false
(s m) == (s n) = m == n

_<_ : ℕ → ℕ → Bool
m < z = false
z < (s n) = true
(s m) < (s n) = m < n

_>_ : ℕ → ℕ → Bool
z > n = false
(s m) > z = true
(s m) > (s n) = m > n
