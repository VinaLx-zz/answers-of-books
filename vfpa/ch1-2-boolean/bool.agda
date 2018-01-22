module bool where

data 𝔹 : Set where
    t : 𝔹
    f : 𝔹

infix 7 ~_
infixl 6 _xor_ _nand_
infixr 6 _&&_
infixr 5 _||_

~_ : 𝔹 → 𝔹
~ t = f
~ f = t

_&&_ : 𝔹 → 𝔹 → 𝔹
t && y = y
f && y = f

_||_ : 𝔹 → 𝔹 → 𝔹
t || y = t
f || y = y

_xor_ : 𝔹 → 𝔹 → 𝔹
t xor b = ~ b
f xor b = b

_nand_ : 𝔹 → 𝔹 → 𝔹
t nand b = ~ b
f nand b = t

if_then_else : ∀ {l} {A : Set l} → 𝔹 -> A -> A -> A
if t then a else b = a
if f then a else b = b
