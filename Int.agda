module Int where

open import Nat
    as ℕ
    using (ℕ)
    renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Equality
open import Sign
    using (Sign)
open import Algebra

data ℤ : Set where
    +_ : ℕ → ℤ
    -[1+_] : ℕ → ℤ
{-# BUILTIN INTEGER ℤ #-}
{-# BUILTIN INTEGERPOS +_ #-}
{-# BUILTIN INTEGERNEGSUC -[1+_] #-}

∣_∣ : ℤ → ℕ
∣ -[1+ x ] ∣ = ℕ.succ x
∣ + x ∣ = x

sign : ℤ → Sign
sign (+ x) = Sign.+
sign -[1+ x ] = Sign.-

_◁_ : Sign → ℕ → ℤ
Sign.+ ◁ n = + n
Sign.- ◁ ℕ.zero = + 0
Sign.- ◁ ℕ.succ n = -[1+ n ]

◁-left-inverse : ∀ n → sign n ◁ ∣ n ∣ ≡ n
◁-left-inverse (+ x) = refl
◁-left-inverse -[1+ x ] = refl

-_ : ℤ → ℤ
- (+ ℕ.zero) = + ℕ.zero
- (+ ℕ.succ x) = -[1+ x ]
- -[1+ x ] = + (ℕ.succ x)

-[-x]=x : ∀ x → - (- x) ≡ x
-[-x]=x (+ ℕ.zero) = refl
-[-x]=x (+ ℕ.succ x) = refl
-[-x]=x -[1+ x ] = refl

_ℕ-_ : ℕ → ℕ → ℤ
x ℕ- ℕ.zero = + x
ℕ.zero ℕ- ℕ.succ y = -[1+ y ]
ℕ.succ x ℕ- ℕ.succ y = x ℕ- y

_+_ : ℤ → ℤ → ℤ
(+ x) + (+ y) = + (x ℕ+ y)
(+ x) + -[1+ y ] = x ℕ- ℕ.succ y
-[1+ x ] + (+ y) = y ℕ- ℕ.succ x
-[1+ x ] + -[1+ y ] = -[1+ ℕ.succ (x ℕ+ y) ]

_-_ : ℤ → ℤ → ℤ
(+ x) - (+ y) = x ℕ- y
-[1+ x ] - (+ y) = -[1+ (x ℕ+ y) ]
(+ x) - -[1+ y ] = + (x ℕ+ ℕ.succ y)
-[1+ x ] - -[1+ y ] = y ℕ- x

x-x=0 : ∀ x → x - x ≡ + 0
x-x=0 (+ ℕ.zero) = refl
x-x=0 (+ ℕ.succ x) = x-x=0 (+ x)
x-x=0 -[1+ ℕ.zero ] = refl
x-x=0 -[1+ ℕ.succ x ] = x-x=0 (+ x)

-- Wild interactively derived proofs :-x
x-y=-[y-x] : ∀ x y → x - y ≡ - (y - x)
x-y=-[y-x] (+ ℕ.zero) (+ ℕ.zero) = refl
x-y=-[y-x] (+ ℕ.zero) (+ ℕ.succ y) = refl
x-y=-[y-x] (+ ℕ.succ x) (+ ℕ.zero) = refl
x-y=-[y-x] (+ ℕ.succ x) (+ ℕ.succ y) = x-y=-[y-x] (+ x) (+ y)
x-y=-[y-x] (+ ℕ.zero) -[1+ ℕ.zero ] = refl
x-y=-[y-x] (+ ℕ.zero) -[1+ ℕ.succ y ] = cong (λ n → + ℕ.succ (ℕ.succ n)) (symm (ℕ.x+0=x y))
x-y=-[y-x] (+ ℕ.succ x) -[1+ ℕ.zero ] = cong (λ n → + ℕ.succ n) (trans (ℕ.swap-succ x ℕ.zero) (cong ℕ.succ (ℕ.x+0=x x)))
x-y=-[y-x] (+ ℕ.succ x) -[1+ ℕ.succ y ] = cong (λ n → + ℕ.succ n) (trans (ℕ.swap-succ x (ℕ.succ y)) (cong ℕ.succ (trans (ℕ.comm-+ x (ℕ.succ y)) {!   !})))
x-y=-[y-x] -[1+ ℕ.zero ] (+ ℕ.zero) = refl
x-y=-[y-x] -[1+ ℕ.zero ] (+ ℕ.succ ℕ.zero) = cong (λ n → -[1+ n ]) refl
x-y=-[y-x] -[1+ ℕ.zero ] (+ ℕ.succ (ℕ.succ y)) = cong (λ n → -[1+ n ]) (cong ℕ.succ {!   !})
x-y=-[y-x] -[1+ ℕ.succ x ] (+ ℕ.zero) = cong (λ n → -[1+ ℕ.succ n ]) (ℕ.x+0=x x)
x-y=-[y-x] -[1+ ℕ.succ x ] (+ ℕ.succ y) = cong (λ n → -[1+ n ]) {!   !}
x-y=-[y-x] -[1+ ℕ.zero ] -[1+ ℕ.zero ] = refl
x-y=-[y-x] -[1+ ℕ.zero ] -[1+ ℕ.succ y ] = refl
x-y=-[y-x] -[1+ ℕ.succ x ] -[1+ ℕ.zero ] = refl
x-y=-[y-x] -[1+ ℕ.succ x ] -[1+ ℕ.succ y ] = x-y=-[y-x] (+ y) (+ x)

module test- where
    5-3=2 : (+ 5) - (+ 3) ≡ (+ 2)
    5-3=2 = refl

    5-7=-2 : (+ 5) - (+ 7) ≡ ((+ 0) - (+ 2))
    5-7=-2 = refl



comm-+ : Commutative _+_
comm-+ (+ x) (+ y) = cong +_ (ℕ.comm-+ x y)
comm-+ (+ x) -[1+ y ] = refl
comm-+ -[1+ x ] (+ y) = refl
comm-+ -[1+ x ] -[1+ y ] = cong (λ n → -[1+ ℕ.succ n ]) (ℕ.comm-+ x y)

assoc-+ : Associative _+_
assoc-+ = {!   !}

x+0=x : RightIdentity _+_ (+ 0)
x+0=x (+ ℕ.zero) = refl
x+0=x (+ ℕ.succ x) = cong (λ n → + ℕ.succ n) (ℕ.x+0=x x)
x+0=x -[1+ _ ] = refl

0+x=x : LeftIdentity _+_ (+ 0)
0+x=x (+ x) = refl
0+x=x -[1+ x ] = refl

ℤ-+0-semigroup : Semigroup _+_
ℤ-+0-semigroup = record { associative = assoc-+ }

ℤ-+0-monoid : Monoid _+_ (+ 0)
ℤ-+0-monoid = record
    { isSemigroup = ℤ-+0-semigroup
    ; identity = record { left  = 0+x=x ; right = x+0=x } }
