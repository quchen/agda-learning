module Int where

open import Nat
    as ℕ
    using (ℕ)
    renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Equality
open import Algebra

data ℤ : Set where
    +_ : ℕ → ℤ
    -[1+_] : ℕ → ℤ

∣_∣ : ℤ → ℕ
∣ -[1+ x ] ∣ = ℕ.succ x
∣ + x ∣ = x

-_ : ℤ → ℤ
- (+ ℕ.zero) = + ℕ.zero
- (+ ℕ.succ x) = -[1+ x ]
- -[1+ x ] = + (ℕ.succ x)

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
-[1+ x ] - (+ y) = {! -[1+ x + y ]  !}
(+ x) - -[1+ y ] = + (x ℕ+ ℕ.succ y)
-[1+ x ] - -[1+ y ] = y ℕ- x

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
