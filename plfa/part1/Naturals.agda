{-# OPTIONS --exact-split #-}

module plfa.part1.Naturals where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)

_ : 2 ≡ suc (suc zero)
_ = refl

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩
    5
  ∎
_ =
  begin
    2 + 3
  ≡⟨⟩
    (suc 1) + 3
  ≡⟨⟩
    (suc (suc 0 + 3))
  ≡⟨⟩
    (suc (suc 3))
  ≡⟨⟩
    5
  ∎

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    (suc (suc (suc zero))) + (suc (suc (suc (suc zero))))
  ≡⟨⟩
    (suc ((suc (suc zero)) + (suc (suc (suc (suc zero))))))
  ≡⟨⟩
    (suc (suc ((suc zero) + (suc (suc (suc (suc zero)))))))
  ≡⟨⟩
    (suc (suc (suc (suc (suc (suc (suc zero)))))))
  ≡⟨⟩
    7
  ∎
_ =
  begin
    3 + 4
  ≡⟨⟩
    (suc 2 + 4)
  ≡⟨⟩
    (suc (suc 1 + 4))
  ≡⟨⟩
    (suc (suc (suc 0 + 4)))
  ≡⟨⟩
    (suc (suc (suc 4)))
  ≡⟨⟩
    7
  ∎

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + (m * n)

_ : 1 * 0 ≡ 0
_ =
  begin
    1 * 0
  ≡⟨⟩
    (suc (zero)) * zero
  ≡⟨⟩
    zero
  ≡⟨⟩
    0
  ∎

_ : 2 * 3 ≡ 6
_ =
  begin
    2 * 3
  ≡⟨⟩
    (suc (suc zero)) * (suc (suc (suc zero)))
  ≡⟨⟩
    (suc (suc (suc zero))) + ((suc zero) * (suc (suc (suc zero))))
  ≡⟨⟩
    (suc (suc (suc zero))) + ((suc (suc (suc zero))) + (zero * (suc (suc (suc zero)))))
  ≡⟨⟩
    (suc (suc (suc zero))) + ((suc (suc (suc zero))) + zero)
  ≡⟨⟩
    (suc (suc (suc zero))) + (suc (suc (suc zero)))
  ≡⟨⟩
    (suc ((suc (suc zero))) + (suc (suc (suc zero))))
  ≡⟨⟩
    (suc (suc ((suc zero + (suc (suc (suc zero)))))))
  ≡⟨⟩
    (suc (suc (suc (suc (suc (suc zero))))))
  ≡⟨⟩
    6
  ∎
_ =
  begin
    2 * 3
  ≡⟨⟩
    3 + (1 * 3)
  ≡⟨⟩
    3 + (3 + (0 * 3))
  ≡⟨⟩
    3 + (3 + 0)
  ≡⟨⟩
    3 + 3
  ≡⟨⟩
    6
  ∎

_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    4 + (4 + 4)
  ≡⟨⟩
    4 + 8
  ≡⟨⟩
    12
  ∎

_^_ : ℕ → ℕ → ℕ
m ^ 0 = suc zero
m ^ suc n = m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩
    3 * (3 * (3 * 3))
  ≡⟨⟩
    3 * (3 * 9)
  ≡⟨⟩
    3 * 27
  ≡⟨⟩
    81
  ∎

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_ : 3 ∸ 2 ≡ 1
_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

_ : 2 ∸ 3 ≡ 0
_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

_ : 5 ∸ 3 ≡ 2
_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

_ : 3 ∸ 5 ≡ 0
_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

infixl 6  _+_  _∸_
infixl 7  _*_

_ : 1 + 2 * 3 ≡ 7
_ =
  begin
    1 + 2 * 3
  ≡⟨⟩
    1 + (2 * 3)
  ≡⟨⟩
    1 + 6
  ≡⟨⟩
    7
  ∎

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc (⟨⟩)  = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

_ : inc (⟨⟩ I O O O) ≡ ⟨⟩ I O O I
_ = refl

_ : inc (⟨⟩ I I I I) ≡ ⟨⟩ I O O O O
_ = refl

to : ℕ → Bin
to zero    = ⟨⟩ O
to (suc n) = inc (to n)

_ : to 0 ≡ ⟨⟩ O
_ = refl

_ : to 1 ≡ ⟨⟩ I
_ = refl

_ : to 2 ≡ ⟨⟩ I O
_ = refl

_ : to 3 ≡ ⟨⟩ I I
_ = refl

_ : to 4 ≡ ⟨⟩ I O O
_ = refl

_ : to 8 ≡ ⟨⟩ I O O O
_ = refl

_ : to 32 ≡ ⟨⟩ I O O O O O
_ = refl


from : Bin → ℕ
from ⟨⟩    = zero
from (b O) = 2 * (from b)
from (b I) = 1 + 2 * (from b)

_ : from (to 0) ≡ 0
_ = refl

_ : from (to 1) ≡ 1
_ = refl

_ : from (to 2) ≡ 2
_ = refl

_ : from (to 3) ≡ 3
_ = refl

_ : from (to 4) ≡ 4
_ = refl

_ : from (to 8) ≡ 8
_ = refl

_ : from (to 32) ≡ 32
_ = refl
