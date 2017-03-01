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

infix 6 _+_
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

comm-+ : (x y : ℕ) → (x + y) ≡ (y + x)
comm-+ zero y = symm-≡ (r-+0-id y)
comm-+ (succ x) y = begin
    succ x + y ≡⟨ refl ⟩
    (1 + x) + y ≡⟨ refl ⟩
    1 + (x + y) ≡⟨ cong-≡ succ (comm-+ x y) ⟩
    1 + (y + x) ≡⟨ refl ⟩
    (1 + y) + x ≡⟨ refl ⟩
    succ y + x ≡⟨ symm-≡ (reorder-succ y x) ⟩
    y + succ x ≡⟨ refl ⟩
    y + succ x qed
  where
    open Equality.≡-Reasoning

    reorder-succ : ∀ x y → (x + succ y) ≡ (succ x + y)
    reorder-succ zero     _ = refl
    reorder-succ (succ x) y = cong-≡ succ (reorder-succ x y)

ℕ-+0-commutative-monoid : CommutativeMonoid _+_ zero
ℕ-+0-commutative-monoid = record
    { isMonoid = ℕ-+0-monoid
    ; commutative = comm-+ }

infix 7 _·_
_·_ : ℕ → ℕ → ℕ
zero   · b = zero
succ a · b = b + (a · b)

0·x=0 : {x : ℕ} → (0 · x) ≡ 0
0·x=0 = refl

x·0=0 : ∀ x → (x · 0) ≡ 0
x·0=0 zero = refl
x·0=0 (succ x) = x·0=0 x

distribute-·+ : ∀ x y z → x · (y + z) ≡ x · y + x · z
distribute-·+ zero _ _ = refl
distribute-·+ (succ x) y z = begin
    succ x · (y + z) ≡⟨ refl ⟩
    (1 + x) · (y + z) ≡⟨ {!   !} ⟩
    succ x · y + succ x · z qed
  where
    open Equality.≡-Reasoning

private
    ·test₁ : (1 · 2) ≡ 2
    ·test₁ = refl

    ·test₂ : (3 · 2) ≡ 6
    ·test₂ = refl

    ·test₃ : (12 · 12) ≡ 144
    ·test₃ = refl

factorial : ℕ → ℕ
factorial zero = 1
factorial (succ x) = succ x · factorial x

private
    factorialTest : factorial 4 ≡ 24
    factorialTest = refl

ℕ-·1-semigroup : Semigroup _·_
ℕ-·1-semigroup = record
    { associative = assoc-· }
  where
    open Equality.≡-Reasoning

    assoc-· : Associative _·_
    assoc-· zero _ _ = refl
    assoc-· (succ x) zero z = assoc-· x zero z
    assoc-· (succ x) (succ y) zero = begin
        (succ x · succ y) · zero ≡⟨ {!   !} ⟩
        succ x · (succ y · zero) ≡⟨ {!   !} ⟩
        succ x · zero ≡⟨ x·0=0 (succ x) ⟩
        zero ≡⟨ {!   !} ⟩
        {!   !} qed

    assoc-· (succ x) (succ y) (succ z) = {!   !}

1·x=x : LeftIdentity _·_ (succ zero)
1·x=x zero = refl
1·x=x (succ x) = begin
    1 · succ x ≡⟨ refl ⟩
    succ (1 · x) ≡⟨ cong-≡ succ (1·x=x x) ⟩
    succ x qed
  where
    open Equality.≡-Reasoning

x·1=x : RightIdentity _·_ (succ zero)
x·1=x zero = refl
x·1=x (succ x) = begin
    succ x · 1 ≡⟨ cong-≡ succ (x·1=x x) ⟩
    succ x qed
  where
    open Equality.≡-Reasoning

ℕ-·1-monoid : Monoid _·_ (succ zero)
ℕ-·1-monoid = record
    { isSemigroup = ℕ-·1-semigroup
    ; identity    = record { left  = 1·x=x
                           ; right = x·1=x } }

comm-· : (x y : ℕ) → (x · y) ≡ (y · x)
comm-· zero y = symm-≡ (x·0=0 y)
comm-· (succ x) y = begin
    succ x · y ≡⟨ refl ⟩
    y + (x · y) ≡⟨ {!   !} ⟩
    y + (y · x) ≡⟨ comm-+ y (y · x) ⟩
    (y · x) + y ≡⟨ {!   !} ⟩
    y · succ x qed
  where
    open Equality.≡-Reasoning

infixr 8 _^_
_^_ : ℕ → ℕ → ℕ
x ^ zero = 1
x ^ succ y = x · x ^ y

private
    test₀ : ∀ {x} → x ^ 0 ≡ 1
    test₀ = refl

    test₂ : 8 ^ 2 ≡ 64
    test₂ = refl

id-right-^ : ∀ x → x ^ 1 ≡ x
id-right-^ zero = refl
id-right-^ (succ x) = cong-≡ succ (id-right-^ x)

1-base : ∀ p → 1 ^ p ≡ 1
1-base zero = refl
1-base (succ p) = begin
    1 ^ succ p ≡⟨ refl ⟩
    1 · (1 ^ p) ≡⟨ 1·x=x (1 ^ p) ⟩
    1 ^ p ≡⟨ 1-base p ⟩
    1 qed
  where
    open Equality.≡-Reasoning

fuse-exponents : ∀ m p q → m ^ p · m ^ q ≡ m ^ (p + q)
fuse-exponents = {!   !}

collapse-tower : ∀ b p q → (b ^ p) ^ q ≡ b ^ (p · q)
collapse-tower = {!   !}
