module Nat where


open import Algebra
open import Equality
open import Logic

open Equality.≡-Reasoning



data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

module test-fromNat where
    test₁ : 1 ≡ succ zero
    test₁ = refl

    test₂ : 2 ≡ succ (succ zero)
    test₂ = refl

    test₃ : 5 ≡ succ (succ (succ (succ (succ zero))))
    test₃ = refl

infix 6 _+_
_+_ : ℕ → ℕ → ℕ
zero   + n = n
succ m + n = succ (m + n)

module test-addition where
    test₁ : (1 + 2) ≡ 3
    test₁ = refl

-- module alternative-+ where
--
--     _+'_ : ℕ → ℕ → ℕ
--     zero   +' n = n
--     succ n +' m = n +' succ m
--
--     +≡ : (m n : ℕ) → succ n +' m ≡ n +' succ m
--     +≡ zero n = refl
--     +≡ (succ m) n = refl
--
--     equivalent-to-+ : (m n : ℕ) → (m + n) ≡ (m +' n)
--     equivalent-to-+ = {!   !}

assoc-+ : Associative _+_
assoc-+ zero     _ _ = refl
assoc-+ (succ x) y z = cong succ (assoc-+ x y z)

ℕ-+0-semigroup : Semigroup _+_
ℕ-+0-semigroup = record { associative = assoc-+ }

x+0=x : RightIdentity _+_ 0
x+0=x zero = refl
x+0=x (succ x) = cong succ (x+0=x x)

0+x=x : LeftIdentity _+_ 0
0+x=x _ = refl

ℕ-+0-monoid : Monoid _+_ 0
ℕ-+0-monoid = record
    { isSemigroup = ℕ-+0-semigroup
    ; identity = record { left  = 0+x=x ; right = x+0=x } }

comm-+ : Commutative _+_
comm-+ zero y = symm (x+0=x y)
comm-+ (succ x) y = begin
    succ x + y ≡⟨ refl ⟩
    (1 + x) + y ≡⟨ refl ⟩
    1 + (x + y) ≡⟨ cong succ (comm-+ x y) ⟩
    1 + (y + x) ≡⟨ refl ⟩
    (1 + y) + x ≡⟨ refl ⟩
    succ y + x ≡⟨ symm (reorder-succ y x) ⟩
    y + succ x ≡⟨ refl ⟩
    y + succ x qed
  where
    reorder-succ : ∀ x y → (x + succ y) ≡ (succ x + y)
    reorder-succ zero     _ = refl
    reorder-succ (succ x) y = cong succ (reorder-succ x y)

ℕ-+0-commutative-monoid : CommutativeMonoid _+_ 0
ℕ-+0-commutative-monoid = record
    { isMonoid = ℕ-+0-monoid
    ; commutative = comm-+ }

infix 6 _-_
_-_ : ℕ → ℕ → ℕ
zero - x = 0
x - zero = x
succ a - succ b = a - b

x-x=0 : ∀ x → x - x ≡ 0
x-x=0 zero = refl
x-x=0 (succ x) = x-x=0 x

x-0=x : RightIdentity _-_ 0
x-0=x zero = refl
x-0=x (succ x) = refl

-- x+y-y=x : ∀ x y → (x + y) - y ≡ x
-- x+y-y=x x zero = begin
--     (x + 0) - 0 ≡⟨ x-0=x (x + 0) ⟩
--     x + 0 ≡⟨ x+0=x x ⟩
--     x qed
-- x+y-y=x x (succ y) = begin
--     (x + succ y) - succ y ≡⟨ {!   !} ⟩
--     (succ x + y) - succ y ≡⟨ refl ⟩
--     succ (x + y) - succ y ≡⟨ refl ⟩
--     (x + y) - y ≡⟨ x+y-y=x x y ⟩
--     x qed

-- x+y-y=x2 : ∀ x y → (x + y) - y ≡ x
-- x+y-y=x2 zero y = x-x=0 y
-- x+y-y=x2 (succ x) y = begin
--     succ (x + y) - y ≡⟨ {!   !} ⟩
--     {!   !}
--     qed


infix 1 _≤_
data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n} → zero ≤ n
    s≤s : ∀ {m n} → m ≤ n → succ m ≤ succ n

n+1>n : ∀ n → ¬ (succ n ≤ n)
n+1>n zero ()
n+1>n (succ n) (s≤s x) = n+1>n n x

n≤n : ∀ n → n ≤ n
n≤n zero = z≤n
n≤n (succ n) = s≤s (n≤n n)

-- Supremely well auto-derivable :-)
m≤m+n : ∀ m n → m ≤ m + n
m≤m+n zero n = z≤n
m≤m+n (succ m) n = s≤s (m≤m+n m n)

¬⟨1+m+n≤m⟩ : ∀ m n → ¬ (succ (m + n) ≤ m)
¬⟨1+m+n≤m⟩ zero n ()
¬⟨1+m+n≤m⟩ (succ m) n (s≤s ¬p) = ¬⟨1+m+n≤m⟩ m n ¬p

m=m+n⇒m≤m+n : ∀ m n → m ≡ m + n → m ≤ (m + n)
m=m+n⇒m≤m+n zero n x = z≤n
m=m+n⇒m≤m+n (succ m) n x = s≤s (m≤m+n m n)

¬⟨m≤n⟩ : ∀ m n → (x : succ (m + ((n - 1) - m)) ≤ m) → ⊥
¬⟨m≤n⟩ m n = ¬⟨1+m+n≤m⟩ m ((n - 1) - m)

module test-≤ where
    test₁ : 1 ≤ 2
    test₁ = s≤s z≤n

    test₂ : 2 ≤ 7
    test₂ = s≤s (s≤s z≤n)

    test₃ : 8 ≤ 8
    test₃ = n≤n 8

    test₄ : ¬ (4 ≤ 3)
    test₄ (s≤s (s≤s (s≤s ())))

    test₅ : ¬ (10 ≤ 7)
    test₅ = ¬⟨1+m+n≤m⟩ 7 ((10 - 1) - 7)

    -- Try auto-deriving this ;-)
    -- test₆ : 22 ≤ 28
    -- test₆ = m=m+n⇒m≤m+n 22 (28 - 22) {!   !}

infix 7 _*_
_*_ : ℕ → ℕ → ℕ
zero   * b = zero
succ a * b = b + (a * b)

0*x=0 : {x : ℕ} → (0 * x) ≡ 0
0*x=0 = refl

x*0=0 : ∀ x → (x * 0) ≡ 0
x*0=0 zero = refl
x*0=0 (succ x) = x*0=0 x

-- distribute-*+ : ∀ x y z → x * (y + z) ≡ x * y + x * z
-- distribute-*+ zero _ _ = refl
-- distribute-*+ (succ x) y z = begin
--     succ x * (y + z) ≡⟨ {!   !} ⟩
--     succ x * y + succ x * z qed

module test-multiplication where
    test₁ : (1 * 2) ≡ 2
    test₁ = refl

    test₂ : (3 * 2) ≡ 6
    test₂ = refl

    test₃ : (12 * 12) ≡ 144
    test₃ = refl

factorial : ℕ → ℕ
factorial zero = 1
factorial (succ x) = succ x * factorial x

module test-factorial where
    test₁ : factorial 4 ≡ 24
    test₁ = refl

-- ℕ-*1-semigroup : Semigroup _*_
-- ℕ-*1-semigroup = record { associative = assoc-* }
--   where
--     assoc-* : Associative _*_
--     assoc-* zero _ _ = refl
--     assoc-* (succ x) zero z = assoc-* x zero z
--     assoc-* (succ x) (succ y) zero = begin
--         (succ x * succ y) * zero ≡⟨ {!   !} ⟩
--         succ x * (succ y * zero) ≡⟨ {!   !} ⟩
--         succ x * zero ≡⟨ x*0=0 (succ x) ⟩
--         zero ≡⟨ {!   !} ⟩
--         {!   !} qed
--
--     assoc-* (succ x) (succ y) (succ z) = {!   !}

1*x=x : LeftIdentity _*_ 1
1*x=x zero = refl
1*x=x (succ x) = begin
    1 * succ x ≡⟨ refl ⟩
    succ (1 * x) ≡⟨ cong succ (1*x=x x) ⟩
    succ x qed

x*1=x : RightIdentity _*_ 1
x*1=x zero = refl
x*1=x (succ x) = begin
    succ x * 1 ≡⟨ cong succ (x*1=x x) ⟩
    succ x qed

-- ℕ-*1-monoid : Monoid _*_ 1
-- ℕ-*1-monoid = record
--     { isSemigroup = ℕ-*1-semigroup
--     ; identity    = record { left  = 1*x=x
--                            ; right = x*1=x } }

-- comm-* : (x y : ℕ) → (x * y) ≡ (y * x)
-- comm-* zero y = symm (x*0=0 y)
-- comm-* (succ x) y = begin
--     succ x * y ≡⟨ refl ⟩
--     y + (x * y) ≡⟨ {!   !} ⟩
--     y + (y * x) ≡⟨ comm-+ y (y * x) ⟩
--     (y * x) + y ≡⟨ {!   !} ⟩
--     y * succ x qed

-- ℕ-*1-commutative-monoid : CommutativeMonoid _*_ 1
-- ℕ-*1-commutative-monoid = record
--     { isMonoid = ℕ-*1-monoid
--     ; commutative = comm-* }

infixr 8 _^_
_^_ : ℕ → ℕ → ℕ
x ^ zero = 1
x ^ succ y = x * x ^ y

module test-exponentiation where
    test₀ : ∀ {x} → x ^ 0 ≡ 1
    test₀ = refl

    test₂ : 8 ^ 2 ≡ 64
    test₂ = refl

id-right-^ : ∀ x → x ^ 1 ≡ x
id-right-^ zero = refl
id-right-^ (succ x) = cong succ (id-right-^ x)

1-base : ∀ p → 1 ^ p ≡ 1
1-base zero = refl
1-base (succ p) = begin
    1 ^ succ p ≡⟨ refl ⟩
    1 * (1 ^ p) ≡⟨ 1*x=x (1 ^ p) ⟩
    1 ^ p ≡⟨ 1-base p ⟩
    1 qed

hyper : (n a b : ℕ) → ℕ
hyper zero a b = b + 1
hyper (succ (succ (succ n))) a zero = 1
hyper (succ (succ n)) a zero = 0
hyper (succ n) a zero = a
hyper (succ n) a (succ b) = hyper n a (hyper (succ n) a b)

module hyper-test where
    testHyper₀ : hyper 0 11 123 ≡ 124
    testHyper₀ = refl

    testHyper₁ : hyper 1 11 0 ≡ 11
    testHyper₁ = refl

    testHyper₂ : hyper 1 11 22 ≡ 11 + 22
    testHyper₂ = refl
