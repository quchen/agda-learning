module Nat where


open import Algebra
open import Equality
open import Logic

data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

import Agda.Builtin.Nat as Nat

fromNat : Nat.Nat → ℕ
fromNat Nat.zero = zero
fromNat (Nat.suc x) = succ (fromNat x)
{-# BUILTIN FROMNAT fromNat #-}

private
    testFromNat : 1 ≡ succ zero
    testFromNat = refl

    testFromNat2 : 2 ≡ succ (succ zero)
    testFromNat2 = refl

    testFromNat5 : 5 ≡ succ (succ (succ (succ (succ zero))))
    testFromNat5 = refl

_+_ : ℕ → ℕ → ℕ
zero   + n = n
succ m + n = succ (m + n)

private
    +test₁ : (1 + 2) ≡ 3
    +test₁ = refl

-- Alternative definition of addition
_+'_ : ℕ → ℕ → ℕ
zero   +' n = n
succ n +' m = n +' succ m

-- Equivalence of the two addition definitions
-- equiv-+-+' : (m n : ℕ) → (m + n) ≡ (m +' n)

assoc-+ : Associative _+_
assoc-+ zero     _ _ = refl
assoc-+ (succ x) y z = cong-≡ succ (assoc-+ x y z)

ℕ-+0-semigroup : Semigroup _+_
ℕ-+0-semigroup = record { associative = assoc-+ }

r-+0-id : RightIdentity _+_ zero
r-+0-id zero = refl
r-+0-id (succ x) = cong-≡ succ (r-+0-id x)

l-+0-id : LeftIdentity _+_ zero
l-+0-id _ = refl

ℕ-+0-monoid : Monoid _+_ zero
ℕ-+0-monoid = record
    { isSemigroup = ℕ-+0-semigroup
    ; identity    = record { left  = l-+0-id
                           ; right = r-+0-id } }

reorder-succ : (x y : ℕ) → (x + succ y) ≡ (succ x + y)
reorder-succ zero     _ = refl
reorder-succ (succ x) y = cong-≡ succ (reorder-succ x y)

comm-+1 : (x : ℕ) → x + 1 ≡ 1 + x
comm-+1 zero = refl
comm-+1 (succ x) = cong-≡ succ (comm-+1 x)

comm-+ : (x y : ℕ) → (x + y) ≡ (y + x)
comm-+ zero y = symm-≡ (r-+0-id y)
comm-+ (succ x) y = {!   !}

_·_ : ℕ → ℕ → ℕ
zero   · b = zero
succ a · b = b + (a · b)

0·x=0 : {x : ℕ} → (0 · x) ≡ 0
0·x=0 = refl

x·0=0 : {x : ℕ} → (x · 0) ≡ 0
x·0=0 {zero} = refl
x·0=0 {succ x} = {!   !}

private
    ·test₁ : (1 · 2) ≡ 2
    ·test₁ = refl

    ·test₂ : (3 · 2) ≡ 6
    ·test₂ = refl

_! : ℕ → ℕ
zero ! = 1
(succ x) ! = succ x · (x !)

factorialTest : (4 !) ≡ 24
factorialTest = refl

ℕ-·1-semigroup : Semigroup _·_
ℕ-·1-semigroup = record
    { associative = assoc-· }
  where
    assoc-· : Associative _·_
    assoc-· = {!   !}

ℕ-·1-monoid : Monoid _·_ (succ zero)
ℕ-·1-monoid = record
    { isSemigroup = ℕ-·1-semigroup
    ; identity    = record { left  = l-id
                           ; right = r-id } }
  where
    l-id : LeftIdentity _·_ (succ zero)
    l-id _ = {!   !}

    r-id : RightIdentity _·_ (succ zero)
    r-id x = {!   !}

comm-· : (a b : ℕ) → (a · b) ≡ (b · a)
comm-· = {!   !}
