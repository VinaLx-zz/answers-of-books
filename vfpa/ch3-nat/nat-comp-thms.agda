module nat-comp-thms where

open import nat
open import Prelude.Bool
open import Prelude.Equality

-- transitivity

<-trans : ∀ {a b c} → a < b ≡ true → b < c ≡ true → a < c ≡ true
<-trans {a} {b} {z} ab ()
<-trans {z} {b} {s cc} ab bc = refl
<-trans {s a} {z} ()
<-trans {s a} {s b} {s c} ab bc = <-trans {a} {b} {c} ab bc

>-trans : ∀ {a b c} → a > b ≡ true → b > c ≡ true → a > c ≡ true
>-trans {z} {b} {c} ()
>-trans {s a} {b} {z} ab bc = refl
>-trans {a} {z} {s c} ab ()
>-trans {s a} {s b} {s c} ab bc = >-trans {a} {b} {c} ab bc
