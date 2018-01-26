module vec where

open import Data.Nat
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality

infixr 6 _::_

data 𝕍 {ℓ} (A : Set ℓ) : ℕ → Set ℓ where
  [] : 𝕍 A zero
  _::_ : ∀ {n : ℕ} → A → 𝕍 A n → 𝕍 A (suc n)

_++_ : ∀ {ℓ} {A : Set ℓ} {m n} → 𝕍 A m → 𝕍 A n → 𝕍 A (m + n)
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

head : ∀ {ℓ} {A : Set ℓ} {n} → 𝕍 A (suc n) → A
head (x :: xs) = x

tail : ∀ {ℓ} {A : Set ℓ} {n} → 𝕍 A n → 𝕍 A (pred n)
tail [] = []
tail (x :: xs) = xs

map : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {n}
      → (A → B) → 𝕍 A n → 𝕍 B n
map f [] = []
map f (x :: xs) = f x :: map f xs

concat : ∀ {ℓ} {A : Set ℓ} {m n} → 𝕍 (𝕍 A n) m → 𝕍 A (m * n)
concat [] = []
concat (v :: vs) = v ++ concat vs

index : ∀ {ℓ} {A : Set ℓ} {m} → (n : ℕ) → 𝕍 A m → {_ : n < m} → A
index n [] {()}
index zero (x :: xs) = x
index (suc n) (x :: xs) {s≤s p} = index n xs {p}

repeat : ∀ {ℓ} {A : Set ℓ} → (n : ℕ) → A → 𝕍 A n
repeat zero a = []
repeat (suc n) a = a :: repeat n a

foldr : ∀ {ℓ ℓ₂} {A : Set ℓ} {B : Set ℓ₂} {n : ℕ} →
        (A → B → B) → B → 𝕍 A n → B
foldr f z [] = z
foldr f z (x :: xs) = f x (foldr f z xs)

zipWith : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {n : ℕ} →
          (A → B → C) → 𝕍 A n → 𝕍 B n → 𝕍 C n
zipWith f [] ys = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

-- ex 5.3

infixr 6 _:-:_

data 𝕃 {ℓ} (A : Set ℓ) : Set ℓ where
  [-] : 𝕃 A
  _:-:_ : A → 𝕃 A → 𝕃 A

length : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → ℕ
length [-] = 0
length (x :-: xs) = suc (length xs)

𝕍→𝕃 : ∀ {ℓ} {A : Set ℓ} {n} → 𝕍 A n → 𝕃 A
𝕍→𝕃 [] = [-]
𝕍→𝕃 (x :: xs) = x :-: 𝕍→𝕃 xs

𝕃→𝕍 : ∀ {ℓ} {A : Set ℓ} → (xs : 𝕃 A) → 𝕍 A (length xs)
𝕃→𝕍 [-] = []
𝕃→𝕍 (x :-: xs) = x :: 𝕃→𝕍 xs

𝕍↔𝕃 : ∀ {ℓ} {A : Set ℓ} {xs : 𝕃 A} → 𝕍→𝕃 (𝕃→𝕍 xs) ≡ xs
𝕍↔𝕃 {xs = [-]} = refl
𝕍↔𝕃 {xs = x :-: xs} rewrite 𝕍↔𝕃 {xs = xs} = refl

-- ex 5.4

unzip : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {n : ℕ} →
        𝕍 (A × B) n → (𝕍 A n × 𝕍 B n)
unzip [] = [] , []
unzip (( a , b ) :: abs) = let ( xs , ys ) = unzip abs
                           in a :: xs , b :: ys

