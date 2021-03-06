module Int where

open import Nat
    as ℕ
    using (ℕ)
    renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Equality
open import Sign
    as Sign
    using (Sign)
    renaming (_*_ to _S*_)
open import Algebra
open import Logic

open Equality.≡-Reasoning



module first-attempt where

    infix 7 +_
    data ℤ : Set where
        +_ : (n : ℕ) → ℤ
        -[1+_] : (n : ℕ) → ℤ
    {-# BUILTIN INTEGER ℤ #-}
    {-# BUILTIN INTEGERPOS +_ #-}
    {-# BUILTIN INTEGERNEGSUC -[1+_] #-}

    ∣_∣ : ℤ → ℕ
    ∣ -[1+ x ] ∣ = ℕ.succ x
    ∣ + x ∣ = x

    sign : ℤ → Sign
    sign (+ _) = Sign.+
    sign -[1+ _ ] = Sign.-

    _◁_ : Sign → ℕ → ℤ
    Sign.+ ◁ n = + n
    Sign.- ◁ ℕ.zero = + 0
    Sign.- ◁ ℕ.succ n = -[1+ n ]

    ◁-inverse : ∀ n → sign n ◁ ∣ n ∣ ≡ n
    ◁-inverse (+ x) = refl
    ◁-inverse -[1+ x ] = refl

    sign²[≠0] : ∀ ±1 x → sign (±1 ◁ ℕ.succ x) ≡ ±1
    sign²[≠0] Sign.+ x = refl
    sign²[≠0] Sign.- x = refl

    sign²[=0] : ∀ ±1 → sign (±1 ◁ 0) ≡ Sign.+
    sign²[=0] Sign.+ = refl
    sign²[=0] Sign.- = refl

    infix 6 _ℕ-_
    _ℕ-_ : ℕ → ℕ → ℤ
    x ℕ- ℕ.zero = + x
    ℕ.zero ℕ- ℕ.succ y = -[1+ y ]
    ℕ.succ x ℕ- ℕ.succ y = x ℕ- y

    infix 8 -_
    -_ : ℤ → ℤ
    - (+ ℕ.zero) = + ℕ.zero
    - (+ ℕ.succ n) = -[1+ n ]
    - -[1+ n ] = + (ℕ.succ n)

    infix 6 _+_
    _+_ : ℤ → ℤ → ℤ
    (+ x) + (+ y) = + (x ℕ+ y)
    (+ x) + -[1+ y ] = x ℕ- ℕ.succ y
    -[1+ x ] + (+ y) = y ℕ- ℕ.succ x
    -[1+ x ] + -[1+ y ] = -[1+ ℕ.succ (x ℕ+ y) ]

    infix 6 _-_
    _-_ : ℤ → ℤ → ℤ
    x - y = x + - y

    -[-x]=x : ∀ x → - (- x) ≡ x
    -[-x]=x (+ ℕ.zero) = refl
    -[-x]=x (+ ℕ.succ x) = refl
    -[-x]=x -[1+ x ] = refl

    -x≡[0-x] : ∀ x → - x ≡ (+ 0) - x
    -x≡[0-x] (+ ℕ.zero) = refl
    -x≡[0-x] (+ ℕ.succ x) = refl
    -x≡[0-x] -[1+ x ] = refl

    module test+- where
        test₁ : (+ 1) + (+ 2) ≡ (+ 3)
        test₁ = refl

        test₂ : (+ 1) + (- (+ 2)) ≡ (- (+ 1))
        test₂ = refl

    x-x≡0 : ∀ x → x - x ≡ + 0
    x-x≡0 (+ ℕ.zero) = refl
    x-x≡0 (+ ℕ.succ n) = x-x≡0 -[1+ n ]
    x-x≡0 -[1+ ℕ.zero ] = refl
    x-x≡0 -[1+ ℕ.succ n ] = x-x≡0 -[1+ n ]

    x-y=-[y-x] : ∀ x y → x - y ≡ - (y - x)
    x-y=-[y-x] (+ ℕ.zero) (+ ℕ.zero) = refl
    x-y=-[y-x] (+ ℕ.zero) (+ ℕ.succ y) rewrite ℕ.x+0≡x y = refl
    x-y=-[y-x] (+ ℕ.succ x) (+ ℕ.zero) rewrite ℕ.x+0≡x x = refl
    x-y=-[y-x] (+ ℕ.succ x) (+ ℕ.succ y) = x-y=-[y-x] -[1+ y ] -[1+ x ]
    x-y=-[y-x] (+ ℕ.zero) -[1+ ℕ.zero ] = refl
    x-y=-[y-x] (+ ℕ.zero) -[1+ ℕ.succ y ] = refl
    x-y=-[y-x] (+ ℕ.succ x) -[1+ ℕ.zero ] rewrite ℕ.comm-+ x 1 = refl
    x-y=-[y-x] (+ ℕ.succ x) -[1+ ℕ.succ y ]
      rewrite ℕ.x+[1+y]≡[1+x]+y x (ℕ.succ y)
            | ℕ.x+[1+y]≡[1+x]+y x y
            | ℕ.comm-+ x y
            = refl
    x-y=-[y-x] -[1+ ℕ.zero ] (+ ℕ.zero) = refl
    x-y=-[y-x] -[1+ ℕ.zero ] (+ ℕ.succ y) rewrite ℕ.comm-+ y 1 = refl
    x-y=-[y-x] -[1+ ℕ.succ x ] (+ ℕ.zero) = refl
    x-y=-[y-x] -[1+ ℕ.succ x ] (+ ℕ.succ y)
      rewrite ℕ.x+[1+y]≡[1+x]+y y (ℕ.succ x)
            | ℕ.x+[1+y]≡[1+x]+y y x
            | ℕ.comm-+ x y
            = refl
    x-y=-[y-x] -[1+ ℕ.zero ] -[1+ ℕ.zero ] = refl
    x-y=-[y-x] -[1+ ℕ.zero ] -[1+ ℕ.succ n ] = refl
    x-y=-[y-x] -[1+ ℕ.succ x ] -[1+ ℕ.zero ] = refl
    x-y=-[y-x] -[1+ ℕ.succ x ] -[1+ ℕ.succ y ] = x-y=-[y-x] -[1+ x ] -[1+ y ]

    module test- where
        5-3=2 : (+ 5) - (+ 3) ≡ (+ 2)
        5-3=2 = refl

        5-7=-2 : (+ 5) - (+ 7) ≡ ((+ 0) - (+ 2))
        5-7=-2 = refl

    comm-+ : Commutative _+_
    comm-+ (+ x) (+ y) rewrite ℕ.comm-+ x y = refl
    comm-+ (+ x) -[1+ y ] = refl
    comm-+ -[1+ x ] (+ y) = refl
    comm-+ -[1+ x ] -[1+ y ] rewrite ℕ.comm-+ x y = refl

    0+x≡x : LeftIdentity _+_ (+ 0)
    0+x≡x (+ _) = refl
    0+x≡x -[1+ _ ] = refl

    x+0≡x : RightIdentity _+_ (+ 0)
    x+0≡x x rewrite comm-+ x (+ 0) = 0+x≡x x

    assoc₁ : ∀ x y z → (x ℕ+ y) ℕ- z ≡ + x + (y ℕ- z)
    assoc₁ _ _  ℕ.zero = refl
    assoc₁ ℕ.zero ℕ.zero (ℕ.succ _) = refl
    assoc₁ ℕ.zero (ℕ.succ y) (ℕ.succ z) = assoc₁ ℕ.zero y z
    assoc₁ (ℕ.succ x) ℕ.zero (ℕ.succ z) rewrite ℕ.x+0≡x x = refl
    assoc₁ (ℕ.succ x) (ℕ.succ y) (ℕ.succ z) = {!   !}

    assoc₂ : ∀ x y z → (y ℕ- x) + + z ≡ (y ℕ+ z) ℕ- x
    assoc₂ ℕ.zero _ _ = refl
    assoc₂ (ℕ.succ _) ℕ.zero _ = refl
    assoc₂ (ℕ.succ x) (ℕ.succ y) z = assoc₂ x y z

    assoc₃ : ∀ x y z → (x ℕ- y) + + z ≡ + x + (z ℕ- y)
    assoc₃ ℕ.zero ℕ.zero _ = refl
    assoc₃ ℕ.zero (ℕ.succ _) ℕ.zero = refl
    assoc₃ ℕ.zero (ℕ.succ y) (ℕ.succ z) = symm (0+x≡x (z ℕ- y))
    assoc₃ (ℕ.succ _) ℕ.zero _ = refl
    assoc₃ (ℕ.succ x) (ℕ.succ y) ℕ.zero = x+0≡x (x ℕ- y)
    assoc₃ (ℕ.succ x) (ℕ.succ y) (ℕ.succ z) = {!   !}

    assoc₄ : ∀ x y z → (x ℕ- y) + -[1+ z ] ≡ x ℕ- (ℕ.succ y ℕ+ z)
    assoc₄ ℕ.zero ℕ.zero z = refl
    assoc₄ ℕ.zero (ℕ.succ _) _ = refl
    assoc₄ (ℕ.succ _) ℕ.zero _ = refl
    assoc₄ (ℕ.succ x) (ℕ.succ y) z = assoc₄ x y z

    assoc₅ : ∀ x y z → (y ℕ- ℕ.succ x) + -[1+ z ] ≡ -[1+ x ] + (y ℕ- ℕ.succ z)
    assoc₅ _ ℕ.zero _ = refl
    assoc₅ ℕ.zero (ℕ.succ _) ℕ.zero = refl
    assoc₅ ℕ.zero (ℕ.succ y) (ℕ.succ z) = {!   !}
    assoc₅ (ℕ.succ x) (ℕ.succ y) ℕ.zero = {!   !}
    assoc₅ (ℕ.succ x) (ℕ.succ y) (ℕ.succ z) = {!   !}

    assoc₆ : ∀ x y z → z ℕ- ℕ.succ (ℕ.succ x ℕ+ y) ≡ -[1+ x ] + (z ℕ- ℕ.succ y)
    assoc₆ _ _ ℕ.zero = refl
    assoc₆ ℕ.zero ℕ.zero (ℕ.succ z) = refl
    assoc₆ ℕ.zero (ℕ.succ y) (ℕ.succ z) = assoc₆ ℕ.zero y z
    assoc₆ (ℕ.succ x) ℕ.zero (ℕ.succ z) = {!   !}
    assoc₆ (ℕ.succ x) (ℕ.succ y) (ℕ.succ z) = {!   !}

    assoc-+ : Associative _+_
    assoc-+ (+ x) (+ y) (+ z) rewrite ℕ.assoc-+ x y z = refl
    assoc-+ (+ x) (+ y) -[1+ z ] = assoc₁ x y (ℕ.succ z)
    assoc-+ (+ x) -[1+ y ] (+ z) = assoc₃ x (ℕ.succ y) z
    assoc-+ (+ x) -[1+ y ] -[1+ z ] = assoc₄ x (ℕ.succ y) z
    assoc-+ -[1+ x ] (+ y) (+ z) = assoc₂ (ℕ.succ x) y z
    assoc-+ -[1+ x ] (+ y) -[1+ z ] = assoc₅ x y z
    assoc-+ -[1+ x ] -[1+ y ] (+ z) = assoc₆ x y z
    assoc-+ -[1+ x ] -[1+ y ] -[1+ z ] rewrite ℕ.x+[1+y]≡[1+x]+y x (y ℕ+ z) | ℕ.assoc-+ x y z = refl

    -- Auto-derive
    left-inverse-+0 : LeftInverse _+_ (+ 0) (-_)
    left-inverse-+0 (+ ℕ.zero) = refl
    left-inverse-+0 (+ ℕ.succ n) = left-inverse-+0 -[1+ n ]
    left-inverse-+0 -[1+ ℕ.zero ] = refl
    left-inverse-+0 -[1+ ℕ.succ n ] = left-inverse-+0 -[1+ n ]

    -- Auto-derive
    right-inverse-+0 : RightInverse _+_ (+ 0) (-_)
    right-inverse-+0 (+ ℕ.zero) = refl
    right-inverse-+0 (+ ℕ.succ n) = right-inverse-+0 -[1+ n ]
    right-inverse-+0 -[1+ ℕ.zero ] = refl
    right-inverse-+0 -[1+ ℕ.succ n ] = right-inverse-+0 -[1+ n ]

    ℤ-+0-abelianGroup : AbelianGroup _+_ (+ 0) (-_)
    ℤ-+0-abelianGroup = record
        { isGroup = record {
            isMonoid = record
                { isSemigroup = record { assoc = assoc-+ }
                ; identity = record
                    { left-id = 0+x≡x
                    ; right-id = x+0≡x } }
            ; inverse-l = left-inverse-+0
            ; inverse-r = right-inverse-+0 }
        ; comm = comm-+ }


    _*_ : ℤ → ℤ → ℤ
    x * y = (sign x S* sign y) ◁ (∣ x ∣ ℕ* ∣ y ∣)

    comm-* : Commutative _*_
    comm-* x y = begin
        (sign x S* sign y) ◁ (∣ x ∣ ℕ* ∣ y ∣) ≡⟨ cong (λ e → (sign x S* sign y) ◁ e) (ℕ.comm-* ∣ x ∣ ∣ y ∣) ⟩
        (sign x S* sign y) ◁ (∣ y ∣ ℕ* ∣ x ∣) ≡⟨ cong (λ e → e ◁ (∣ y ∣ ℕ* ∣ x ∣)) (Sign.comm-* (sign x) (sign y)) ⟩
        (sign y S* sign x) ◁ (∣ y ∣ ℕ* ∣ x ∣) qed

    assoc-* : Associative _*_
    assoc-* = {!   !}

    1*x≡x : LeftIdentity _*_ (+ 1)
    1*x≡x (+ ℕ.zero) = refl
    1*x≡x (+ ℕ.succ x) =
        begin
            (+ ℕ.succ (x ℕ+ ℕ.zero))
        ≡⟨ cong (λ e → + ℕ.succ e) (ℕ.x+0≡x x) ⟩
            (+ ℕ.succ x)
        qed
    1*x≡x -[1+ ℕ.zero ] = refl
    1*x≡x -[1+ ℕ.succ x ] =
        begin
            -[1+ ℕ.succ (x ℕ+ ℕ.zero) ]
        ≡⟨ cong (λ e → -[1+ ℕ.succ e ]) (ℕ.x+0≡x x) ⟩
            -[1+ ℕ.succ x ]
        qed

    x*1≡x : RightIdentity _*_ (+ 1)
    x*1≡x x =
        begin
            (x * (+ 1))
        ≡⟨ symm (comm-* (+ ℕ.succ ℕ.zero) x) ⟩
            ((+ 1) * x)
        ≡⟨ 1*x≡x x ⟩
            x
        qed

module second-attempt where

    signℤ : ℕ → Set
    signℤ ℕ.zero = ⊤
    signℤ (ℕ.succ x) = Sign

    data ℤ : Set where
        mkℤ : (n : ℕ) → (s : signℤ n) → ℤ

    ∣_∣ : ℤ → ℕ
    ∣ mkℤ n _ ∣ = n

    sign : ℤ → Sign
    sign (mkℤ ℕ.zero tt) = Sign.+
    sign (mkℤ (ℕ.succ _) Sign.+) = Sign.+
    sign (mkℤ (ℕ.succ _) Sign.-) = Sign.-

    _◁_ : Sign → ℕ → ℤ
    _ ◁ ℕ.zero = mkℤ ℕ.zero tt
    s ◁ ℕ.succ n = mkℤ (ℕ.succ n) s

    fromℕ : ℕ → ℤ
    fromℕ x = Sign.+ ◁ x

    ◁-left-inverse : ∀ n → sign n ◁ ∣ n ∣ ≡ n
    ◁-left-inverse (mkℤ ℕ.zero tt) = refl
    ◁-left-inverse (mkℤ (ℕ.succ n) Sign.+) = refl
    ◁-left-inverse (mkℤ (ℕ.succ n) Sign.-) = refl

    _ℕ-_ : ℕ → ℕ → ℤ
    x ℕ- ℕ.zero = Sign.+ ◁ x
    ℕ.zero ℕ- ℕ.succ y = Sign.- ◁ y
    ℕ.succ x ℕ- ℕ.succ y = x ℕ- y

    xℕ-x≡0 : ∀ {n} → n ℕ- n ≡ fromℕ 0
    xℕ-x≡0 {ℕ.zero} = refl
    xℕ-x≡0 {ℕ.succ n} = xℕ-x≡0 {n}

    -_ : ℤ → ℤ
    - mkℤ ℕ.zero tt = mkℤ ℕ.zero tt
    - mkℤ (ℕ.succ n) s = mkℤ (ℕ.succ n) (s Sign.* Sign.-)

    _+_ : ℤ → ℤ → ℤ
    mkℤ ℕ.zero _ + y = y
    x + mkℤ ℕ.zero _ = x
    mkℤ (ℕ.succ x) Sign.+ + mkℤ (ℕ.succ y) Sign.+ = Sign.+ ◁ (ℕ.succ x ℕ+ ℕ.succ y)
    mkℤ (ℕ.succ x) Sign.+ + mkℤ (ℕ.succ y) Sign.- = ℕ.succ x ℕ- ℕ.succ y
    mkℤ (ℕ.succ x) Sign.- + mkℤ (ℕ.succ y) Sign.+ = - (ℕ.succ y ℕ- ℕ.succ x)
    mkℤ (ℕ.succ x) Sign.- + mkℤ (ℕ.succ y) Sign.- = Sign.- ◁ (ℕ.succ x ℕ+ ℕ.succ y)

    _-_ : ℤ → ℤ → ℤ
    x - mkℤ ℕ.zero tt = x
    x - mkℤ (ℕ.succ n) Sign.+ = x + mkℤ (ℕ.succ n) Sign.-
    x - mkℤ (ℕ.succ n) Sign.- = x + mkℤ (ℕ.succ n) Sign.+

    -[-x]=x : ∀ {x} → - (- x) ≡ x
    -[-x]=x {mkℤ ℕ.zero tt} = refl
    -[-x]=x {mkℤ (ℕ.succ n) Sign.+} = refl
    -[-x]=x {mkℤ (ℕ.succ n) Sign.-} = refl

    -x≡[0-x] : ∀ {x} → - x ≡ fromℕ 0 - x
    -x≡[0-x] {mkℤ ℕ.zero tt} = refl
    -x≡[0-x] {mkℤ (ℕ.succ n) Sign.+} = refl
    -x≡[0-x] {mkℤ (ℕ.succ n) Sign.-} = refl

    -- Ha! My first use of »rewrite«. Pretty handy, although I don’t fully
    -- understand its inner workings yet (despite having seen the with-clause
    -- it desugars to).
    x-x≡0 : ∀ {x} → x - x ≡ fromℕ 0
    x-x≡0 {mkℤ ℕ.zero tt} = refl
    x-x≡0 {mkℤ (ℕ.succ n) Sign.+} rewrite xℕ-x≡0 {n} = refl
    x-x≡0 {mkℤ (ℕ.succ n) Sign.-} rewrite xℕ-x≡0 {n} = refl

    x+0≡x : RightIdentity _+_ (fromℕ 0)
    x+0≡x (mkℤ ℕ.zero tt) = refl
    x+0≡x (mkℤ (ℕ.succ n) Sign.+) = refl
    x+0≡x (mkℤ (ℕ.succ n) Sign.-) = refl

    0+x≡x : LeftIdentity _+_ (fromℕ 0)
    0+x≡x (mkℤ ℕ.zero tt) = refl
    0+x≡x (mkℤ (ℕ.succ n) Sign.+) = refl
    0+x≡x (mkℤ (ℕ.succ n) Sign.-) = refl

    comm-+ : Commutative _+_
    comm-+ (mkℤ ℕ.zero tt) (mkℤ ℕ.zero tt) = refl
    comm-+ (mkℤ ℕ.zero tt) (mkℤ (ℕ.succ _) _) = refl
    comm-+ (mkℤ (ℕ.succ _) _) (mkℤ ℕ.zero tt) = refl
    comm-+ (mkℤ (ℕ.succ n) Sign.+) (mkℤ (ℕ.succ n₁) Sign.+) = {!   !}
    comm-+ (mkℤ (ℕ.succ n) Sign.+) (mkℤ (ℕ.succ n₁) Sign.-) = {!   !}
    comm-+ (mkℤ (ℕ.succ n) Sign.-) (mkℤ (ℕ.succ n₁) Sign.+) = {!   !}
    comm-+ (mkℤ (ℕ.succ n) Sign.-) (mkℤ (ℕ.succ n₁) Sign.-) = {!   !}

    _*_ : ℤ → ℤ → ℤ
    mkℤ ℕ.zero _ * _ = mkℤ ℕ.zero tt
    _ * mkℤ ℕ.zero _ = mkℤ ℕ.zero tt
    mkℤ (ℕ.succ n₁) s₁ * mkℤ (ℕ.succ n₂) s₂ = (s₁ Sign.* s₂) ◁ (ℕ.succ n₁ ℕ.* ℕ.succ n₂)

    x*1≡x : RightIdentity _*_ (fromℕ 1)
    x*1≡x (mkℤ ℕ.zero tt) = refl
    x*1≡x (mkℤ (ℕ.succ n) s) rewrite ℕ.x*1≡x n | Sign.x*+≡x s = refl

    1*x≡x : LeftIdentity _*_ (fromℕ 1)
    1*x≡x (mkℤ ℕ.zero tt) = refl
    1*x≡x (mkℤ (ℕ.succ n) s) rewrite ℕ.1*x≡x n | Sign.+*x≡x s = refl

    comm-* : Commutative _*_
    comm-* (mkℤ ℕ.zero tt) (mkℤ ℕ.zero tt) = refl
    comm-* (mkℤ ℕ.zero _) (mkℤ (ℕ.succ _) _) = refl
    comm-* (mkℤ (ℕ.succ _) _) (mkℤ ℕ.zero _) = refl
    comm-* (mkℤ (ℕ.succ a) Sign.+) (mkℤ (ℕ.succ b) Sign.+) = {!   !}
    comm-* (mkℤ (ℕ.succ a) Sign.+) (mkℤ (ℕ.succ b) Sign.-) = {!   !}
    comm-* (mkℤ (ℕ.succ a) Sign.-) (mkℤ (ℕ.succ b) Sign.+) = {!   !}
    comm-* (mkℤ (ℕ.succ a) Sign.-) (mkℤ (ℕ.succ b) Sign.-) = {!   !}
