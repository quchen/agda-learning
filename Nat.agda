module Nat where



open import Algebra
open import Equality
open import Logic

open Equality.≡-Reasoning
open Logic.Decidable.Binary



data ℕ : Set where
    zero : ℕ
    succ : (n : ℕ) → ℕ
{-# BUILTIN NATURAL ℕ #-}

equality-of-successors : ∀ {m n} → succ m ≡ succ n → m ≡ n
equality-of-successors refl = refl

_≟_ : Decidable {A = ℕ} _≡_
zero ≟ zero = yes refl
zero ≟ succ y = no (λ ())
succ x ≟ zero = no (λ ())
succ x ≟ succ y with x ≟ y
succ x ≟ succ .x | yes refl = yes refl
succ x ≟ succ y | no x≢y = no (λ pSucc → x≢y (equality-of-successors pSucc))

rec-ℕ : {C : Set} → C → (ℕ → C → C) → ℕ → C
rec-ℕ z _ zero = z
rec-ℕ z s (succ n) = s n (rec-ℕ z s n)

ind-ℕ : {C : ℕ → Set} → C 0 → ((n : ℕ) → C n → C (succ n)) → (x : ℕ) → C x
ind-ℕ z _ zero = z
ind-ℕ z s (succ n) = s n (ind-ℕ z s n)

private
    -- Like in the Bool module: how does this work? Why don’t I have to
    -- instantiate ind-ℕ with {λ _ → C}?
    rec-via-ind : {C : Set} → C → (ℕ → C → C) → ℕ → C
    rec-via-ind = ind-ℕ

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
    test₁ : 1 + 2 ≡ 3
    test₁ = refl

module rec-addition where
    _+rec_ : ℕ → ℕ → ℕ
    x +rec y = rec-ℕ y (λ _ n → succ n) x

    test₁ : 1 +rec 2 ≡ 3
    test₁ = refl

    test₂ : 12 +rec 23 ≡ 35
    test₂ = refl

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
--     -- Woah, can’t prove this. Such a simple theorem!
--     equivalent-to-+ : (m n : ℕ) → m + n ≡ m +' n
--     equivalent-to-+ = {!   !}

assoc-+ : Associative _+_
assoc-+ zero     _ _ = refl
assoc-+ (succ x) y z = cong succ (assoc-+ x y z)

private
    assoc-+-rewrite : Associative _+_
    assoc-+-rewrite zero     _ _ = refl
    assoc-+-rewrite (succ x) y z rewrite assoc-+-rewrite x y z = refl

ℕ-+0-semigroup : Semigroup _+_
ℕ-+0-semigroup = record { assoc = assoc-+ }

x+0≡x : RightIdentity _+_ 0
x+0≡x zero = refl
x+0≡x (succ x) = cong succ (x+0≡x x)

0+x≡x : LeftIdentity _+_ 0
0+x≡x _ = refl

ℕ-+0-monoid : Monoid _+_ 0
ℕ-+0-monoid = record
    { isSemigroup = ℕ-+0-semigroup
    ; identity = record { left-id  = 0+x≡x ; right-id = x+0≡x } }

x+[1+y]≡[1+x]+y : ∀ x y → (x + succ y) ≡ (succ x + y)
x+[1+y]≡[1+x]+y zero     _ = refl
x+[1+y]≡[1+x]+y (succ x) y rewrite x+[1+y]≡[1+x]+y x y = refl

comm-+ : Commutative _+_
comm-+ zero y = symm (x+0≡x y)
comm-+ (succ x) y = begin
    succ x + y ≡⟨ refl ⟩
    (1 + x) + y ≡⟨ refl ⟩
    1 + (x + y) ≡⟨ cong succ (comm-+ x y) ⟩
    1 + (y + x) ≡⟨ refl ⟩
    (1 + y) + x ≡⟨ refl ⟩
    succ y + x ≡⟨ symm (x+[1+y]≡[1+x]+y y x) ⟩
    y + succ x qed

private
    comm-+-rewrite : Commutative _+_
    comm-+-rewrite zero y = symm (x+0≡x y)
    comm-+-rewrite (succ x) y rewrite comm-+ x y | x+[1+y]≡[1+x]+y y x = refl

ℕ-+0-commutative-monoid : CommutativeMonoid _+_ 0
ℕ-+0-commutative-monoid = record
    { isMonoid = ℕ-+0-monoid
    ; comm = comm-+ }

infix 6 _∸_
_∸_ : ℕ → ℕ → ℕ
zero ∸ x = 0
x ∸ zero = x
succ a ∸ succ b = a ∸ b

x∸x≡0 : ∀ x → x ∸ x ≡ 0
x∸x≡0 zero = refl
x∸x≡0 (succ x) = x∸x≡0 x

x∸0≡x : RightIdentity _∸_ 0
x∸0≡x zero = refl
x∸0≡x (succ x) = refl

[x+y]∸y≡x : ∀ x y → (x + y) ∸ y ≡ x
[x+y]∸y≡x x zero rewrite x+0≡x x | x∸0≡x x = refl
[x+y]∸y≡x x (succ y) rewrite x+[1+y]≡[1+x]+y x y | [x+y]∸y≡x x y = refl

infix 1 _≤_
data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n} → zero ≤ n
    s≤s : ∀ {m n} → m ≤ n → succ m ≤ succ n

infix 1 _<_
_<_ : ℕ → ℕ → Set
a < b = succ a ≤ b

pred-≤ : ∀ {m n} → succ m ≤ succ n → m ≤ n
pred-≤ (s≤s x) = x

n+1>n : ∀ n → ¬ (succ n ≤ n)
n+1>n zero ()
n+1>n (succ n) (s≤s x) = n+1>n n x

refl-≤ : ∀ {n} → n ≤ n
refl-≤ {zero} = z≤n
refl-≤ {succ n} = s≤s refl-≤

-- ≤ separates points
sep-≤ : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b
sep-≤ z≤n z≤n = refl
sep-≤ (s≤s a≤b) (s≤s b≤a) rewrite sep-≤ a≤b b≤a = refl

trans-≤ : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
trans-≤ z≤n _ = z≤n
trans-≤ (s≤s a≤b) (s≤s b≤c) = s≤s (trans-≤ a≤b b≤c)

m≡n⇒m≤n : ∀ m n → m ≡ n → m ≤ n
m≡n⇒m≤n m n x = subst (λ e → e ≤ n) (symm x) refl-≤

-- Supremely well auto-derivable :-)
m≤m+n : ∀ m n → m ≤ m + n
m≤m+n zero n = z≤n
m≤m+n (succ m) n = s≤s (m≤m+n m n)

¬⟨1+m+n≤m⟩ : ∀ m n → ¬ (succ (m + n) ≤ m)
¬⟨1+m+n≤m⟩ zero n ()
¬⟨1+m+n≤m⟩ (succ m) n (s≤s ¬p) = ¬⟨1+m+n≤m⟩ m n ¬p

¬1+m≤m : ∀ m → ¬ (succ m ≤ m)
¬1+m≤m zero ()
¬1+m≤m (succ m) (s≤s x) = ¬1+m≤m m x

¬⟨m≤n⟩ : ∀ m n → (x : succ (m + ((n ∸ 1) ∸ m)) ≤ m) → ⊥
¬⟨m≤n⟩ m n = ¬⟨1+m+n≤m⟩ m ((n ∸ 1) ∸ m)

bigger-ℕ-exists : ∀ a → ∃ (λ b → a < b)
bigger-ℕ-exists n = succ n , refl-≤

x-y≡0 : ∀ x y → x ≤ y → x ∸ y ≡ 0
x-y≡0 zero y x₁ = refl
x-y≡0 (succ x) _ (s≤s {n = n} e) = x-y≡0 x n e

_≤?_ : Decidable _≤_
zero ≤? zero = yes z≤n
zero ≤? succ y = yes z≤n
succ x ≤? zero = no (λ ())
succ x ≤? succ y with x ≤? y
succ x ≤? succ y | yes x≤y = yes (s≤s x≤y)
succ x ≤? succ y | no x≰y = no (λ ≤succ → x≰y (pred-≤ ≤succ))

module test-≤ where
    test₁ : 1 ≤ 2
    test₁ = s≤s z≤n

    test₂ : 2 ≤ 7
    test₂ = s≤s (s≤s z≤n)

    test₃ : 8 ≤ 8
    test₃ = refl-≤

    test₄ : ¬ (4 ≤ 3)
    test₄ (s≤s (s≤s (s≤s ())))

    test₅ : ¬ (10 ≤ 7)
    test₅ = ¬⟨1+m+n≤m⟩ 7 ((10 ∸ 1) ∸ 7)

    -- Try auto-deriving this proof ;-)
    test₆ : 222 ≤ 228
    test₆ = m≤m+n 222 (228 ∸ 222)

module test< where
    x : 1 < 2
    x = s≤s (s≤s z≤n)

    y : ¬ (1 < 1)
    y = ¬⟨m≤n⟩ 1 0

    z : ¬ (1 < 0)
    z = ¬⟨m≤n⟩ 0 2

infix 7 _*_
_*_ : ℕ → ℕ → ℕ
zero   * b = zero
succ a * b = b + (a * b)

0*x≡0 : ∀ x → (0 * x) ≡ 0
0*x≡0 _ = refl

x*0≡0 : ∀ x → (x * 0) ≡ 0
x*0≡0 zero = refl
x*0≡0 (succ x) = x*0≡0 x

-- The arguments to comm and assoc are nicely auto-derivable.
distribute-*+ : ∀ x y z → x * (y + z) ≡ x * y + x * z
distribute-*+ zero _ _ = refl
distribute-*+ (succ x) y z
  rewrite distribute-*+ x y z
        | symm (assoc-+ (y + z) (x * y) (x * z))
        | comm-+ y z
        | assoc-+ z y (x * y)
        | comm-+ z (y + x * y)
        | assoc-+ (y + x * y) z (x * z)
       = refl

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

1*x≡x : LeftIdentity _*_ 1
1*x≡x zero = refl
1*x≡x (succ x) rewrite x+0≡x x = refl

x*1≡x : RightIdentity _*_ 1
x*1≡x zero = refl
x*1≡x (succ x) rewrite x*1≡x x = refl

comm-* : Commutative _*_
comm-* zero y = symm (x*0≡0 y)
comm-* (succ x) y = begin
    succ x * y    ≡⟨ refl ⟩
    y + x * y     ≡⟨ cong (λ e → y + e) (comm-* x y) ⟩
    y + y * x     ≡⟨ cong (λ e → e + y * x) (symm (x*1≡x y)) ⟩
    y * 1 + y * x ≡⟨ symm (distribute-*+ y 1 x) ⟩
    y * (1 + x)   ≡⟨ refl ⟩
    y * succ x    qed

assoc-* : Associative _*_
assoc-* zero y z = refl
assoc-* (succ x) y z = begin
    (succ x * y) * z    ≡⟨ refl ⟩
    (y + x * y) * z     ≡⟨ comm-* (y + x * y) z ⟩
    z * (y + x * y)     ≡⟨ distribute-*+ z y (x * y) ⟩
    z * y + z * (x * y) ≡⟨ cong (λ e → e + z * (x * y)) (comm-* z y) ⟩
    y * z + z * (x * y) ≡⟨ cong (λ e → y * z + e) (comm-* z (x * y)) ⟩
    y * z + (x * y) * z ≡⟨ cong (λ e → y * z + e) (assoc-* x y z) ⟩
    y * z + x * (y * z) ≡⟨ refl ⟩
    (1 + x) * (y * z)   ≡⟨ refl ⟩
    succ x * (y * z)    qed

ℕ-*1-semigroup : Semigroup _*_
ℕ-*1-semigroup = record { assoc = assoc-* }

ℕ-*1-monoid : Monoid _*_ 1
ℕ-*1-monoid = record
    { isSemigroup = ℕ-*1-semigroup
    ; identity    = record { left-id  = 1*x≡x
                           ; right-id = x*1≡x } }

ℕ-*1-commutative-monoid : CommutativeMonoid _*_ 1
ℕ-*1-commutative-monoid = record
    { isMonoid = ℕ-*1-monoid
    ; comm = comm-* }

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

1^e≡1 : ∀ e → 1 ^ e ≡ 1
1^e≡1 zero = refl
1^e≡1 (succ e) = begin
    1 ^ succ e  ≡⟨ refl ⟩
    1 * (1 ^ e) ≡⟨ 1*x≡x (1 ^ e) ⟩
    1 ^ e       ≡⟨ 1^e≡1 e ⟩
    1           qed

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

    test[n=0] : ∀ a b → hyper 0 a b ≡ b + 1
    test[n=0] _ _ = refl

    [n=1]⇒+ : ∀ a b → hyper 1 a b ≡ a + b
    [n=1]⇒+ zero zero = refl
    [n=1]⇒+ zero (succ b) = begin
            hyper 1 0 b + 1
        ≡⟨ comm-+ (hyper 1 0 b) 1 ⟩
            1 + hyper 1 0 b
        ≡⟨ refl ⟩
            succ (hyper 1 0 b)
        ≡⟨ cong succ ([n=1]⇒+ zero b) ⟩
            succ b
        qed
    [n=1]⇒+ (succ a) zero = cong succ (symm (x+0≡x a))
    [n=1]⇒+ (succ a) (succ b) = begin
            hyper 1 (succ a) b + 1
        ≡⟨ comm-+ (hyper 1 (succ a) b) 1 ⟩
            1 + hyper 1 (succ a) b
        ≡⟨ refl ⟩
            succ (hyper 1 (succ a) b)
        ≡⟨ cong succ (trans ([n=1]⇒+ (succ a) b) (symm (x+[1+y]≡[1+x]+y a b)))  ⟩
            succ (a + succ b)
        qed

_⊓_ : ℕ → ℕ → ℕ
zero ⊓ b = zero
a ⊓ zero = zero
succ a ⊓ succ b = succ (a ⊓ b)

_⊔_ : ℕ → ℕ → ℕ
zero ⊔ b = b
a ⊔ zero = a
succ a ⊔ succ b = succ (a ⊔ b)

0⊔x≡x : LeftIdentity _⊔_ 0
0⊔x≡x _ = refl

x⊔0≡x : RightIdentity _⊔_ 0
x⊔0≡x zero = refl
x⊔0≡x (succ _) = refl

assoc-⊔ : Associative _⊔_
assoc-⊔ zero y z = refl
assoc-⊔ (succ x) zero z = refl
assoc-⊔ (succ x) (succ y) zero = refl
assoc-⊔ (succ x) (succ y) (succ z) rewrite assoc-⊔ x y z = refl

comm-⊔ : Commutative _⊔_
comm-⊔ zero zero = refl
comm-⊔ zero (succ y) = refl
comm-⊔ (succ x) zero = refl
comm-⊔ (succ x) (succ y) rewrite comm-⊔ x y = refl

semigroup-⊔ : Semigroup _⊔_
semigroup-⊔ = record { assoc = assoc-⊔ }

monoid-⊔ : Monoid _⊔_ 0
monoid-⊔ = record
    { isSemigroup = semigroup-⊔
    ; identity = record { left-id = 0⊔x≡x ; right-id = x⊔0≡x } }

commutative-monoid-⊔ : CommutativeMonoid _⊔_ 0
commutative-monoid-⊔ = record { isMonoid = monoid-⊔ ; comm = comm-⊔ }

assoc-⊓ : Associative _⊓_
assoc-⊓ zero y z = refl
assoc-⊓ (succ x) zero z = refl
assoc-⊓ (succ x) (succ y) zero = refl
assoc-⊓ (succ x) (succ y) (succ z) rewrite assoc-⊓ x y z = refl

comm-⊓ : Commutative _⊓_
comm-⊓ zero zero = refl
comm-⊓ zero (succ y) = refl
comm-⊓ (succ x) zero = refl
comm-⊓ (succ x) (succ y) rewrite comm-⊓ x y = refl

semigroup-⊓ : Semigroup _⊓_
semigroup-⊓ = record { assoc = assoc-⊓ }

⊔-picks-greater : ∀ {a b} → a ≤ b → a ⊔ b ≡ b
⊔-picks-greater z≤n = refl
⊔-picks-greater (s≤s x) rewrite ⊔-picks-greater x = refl

max : ℕ → ℕ → ℕ
max = _⊔_

⊓-picks-smaller : ∀ {a b} → a ≤ b → a ⊓ b ≡ a
⊓-picks-smaller z≤n = refl
⊓-picks-smaller (s≤s x) rewrite ⊓-picks-smaller x = refl

min : ℕ → ℕ → ℕ
min = _⊓_

module min-max-test where
    test₁ : 1 ⊓ 2 ≡ 1
    test₁ = refl

    test₂ : 1 ⊔ 2 ≡ 2
    test₂ = refl

    test₃ : min 1 2 ≡ 1
    test₃ = refl

    test₄ : max 1 2 ≡ 2
    test₄ = refl
