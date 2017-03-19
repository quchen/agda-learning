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
    sign (+ x) = Sign.+
    sign -[1+ x ] = Sign.-

    _◁_ : Sign → ℕ → ℤ
    Sign.+ ◁ n = + n
    Sign.- ◁ ℕ.zero = + 0
    Sign.- ◁ ℕ.succ n = -[1+ n ]

    ◁-left-inverse : ∀ n → sign n ◁ ∣ n ∣ ≡ n
    ◁-left-inverse (+ x) = refl
    ◁-left-inverse -[1+ x ] = refl

    sign²[≠0] : ∀ ±1 x → sign (±1 ◁ ℕ.succ x) ≡ ±1
    sign²[≠0] Sign.+ x = refl
    sign²[≠0] Sign.- x = refl

    sign²[=0] : ∀ ±1 → sign (±1 ◁ 0) ≡ Sign.+
    sign²[=0] Sign.+ = refl
    sign²[=0] Sign.- = refl

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

    -_ : ℤ → ℤ
    - x = (+ 0) - x

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
    x-x≡0 (+ ℕ.succ x) = x-x≡0 (+ x)
    x-x≡0 -[1+ ℕ.zero ] = refl
    x-x≡0 -[1+ ℕ.succ x ] = x-x≡0 (+ x)

    -- Wild interactively derived proofs :-x
    x-y=-[y-x] : ∀ x y → x - y ≡ - (y - x)
    x-y=-[y-x] (+ ℕ.zero) (+ ℕ.zero) = refl
    x-y=-[y-x] (+ ℕ.zero) (+ ℕ.succ y) = refl
    x-y=-[y-x] (+ ℕ.succ x) (+ ℕ.zero) = refl
    x-y=-[y-x] (+ ℕ.succ x) (+ ℕ.succ y) = x-y=-[y-x] (+ x) (+ y)
    x-y=-[y-x] (+ ℕ.zero) -[1+ ℕ.zero ] = refl
    x-y=-[y-x] (+ ℕ.zero) -[1+ ℕ.succ y ] = cong (λ n → + ℕ.succ (ℕ.succ n)) (symm (ℕ.x+0≡x y))
    x-y=-[y-x] (+ ℕ.succ x) -[1+ ℕ.zero ] = cong (λ n → + ℕ.succ n) (trans (ℕ.x+[1+y]≡[1+x]+y x ℕ.zero) (cong ℕ.succ (ℕ.x+0≡x x)))
    x-y=-[y-x] (+ ℕ.succ x) -[1+ ℕ.succ y ] = cong (λ n → + ℕ.succ n) (trans (ℕ.x+[1+y]≡[1+x]+y x (ℕ.succ y)) (cong ℕ.succ (trans (ℕ.comm-+ x (ℕ.succ y)) (symm (ℕ.x+[1+y]≡[1+x]+y y x)))))
    x-y=-[y-x] -[1+ ℕ.zero ] (+ ℕ.zero) = refl
    x-y=-[y-x] -[1+ ℕ.zero ] (+ ℕ.succ ℕ.zero) = cong (λ n → -[1+ n ]) refl
    x-y=-[y-x] -[1+ ℕ.zero ] (+ ℕ.succ (ℕ.succ y)) = cong (λ n → -[1+ n ]) (cong ℕ.succ (symm (trans (ℕ.comm-+ y (ℕ.succ ℕ.zero)) refl)))
    x-y=-[y-x] -[1+ ℕ.succ x ] (+ ℕ.zero) = cong (λ n → -[1+ ℕ.succ n ]) (ℕ.x+0≡x x)
    x-y=-[y-x] -[1+ ℕ.succ x ] (+ ℕ.succ y) = cong (λ n → -[1+ n ]) (begin ℕ.succ (x ℕ+ ℕ.succ y) ≡⟨ ℕ.comm-+ (ℕ.succ x) (ℕ.succ y) ⟩ ℕ.succ y ℕ+ ℕ.succ x ≡⟨ symm (ℕ.x+[1+y]≡[1+x]+y y (ℕ.succ x)) ⟩ y ℕ+ ℕ.succ (ℕ.succ x) qed)
    x-y=-[y-x] -[1+ ℕ.zero ] -[1+ ℕ.zero ] = refl
    x-y=-[y-x] -[1+ ℕ.zero ] -[1+ ℕ.succ y ] = refl
    x-y=-[y-x] -[1+ ℕ.succ x ] -[1+ ℕ.zero ] = refl
    x-y=-[y-x] -[1+ ℕ.succ x ] -[1+ ℕ.succ y ] = x-y=-[y-x] (+ y) (+ x)

    module test- where
        5-3=2 : (+ 5) - (+ 3) ≡ (+ 2)
        5-3=2 = refl

        5-7=-2 : (+ 5) - (+ 7) ≡ ((+ 0) - (+ 2))
        5-7=-2 = refl

    x+0≡x : RightIdentity _+_ (+ 0)
    x+0≡x (+ ℕ.zero) = refl
    x+0≡x (+ ℕ.succ x) = cong (λ n → + ℕ.succ n) (ℕ.x+0≡x x)
    x+0≡x -[1+ _ ] = refl

    0+x≡x : LeftIdentity _+_ (+ 0)
    0+x≡x (+ x) = refl
    0+x≡x -[1+ x ] = refl

    comm-+ : Commutative _+_
    comm-+ (+ x) (+ y) = cong +_ (ℕ.comm-+ x y)
    comm-+ (+ x) -[1+ y ] = refl
    comm-+ -[1+ x ] (+ y) = refl
    comm-+ -[1+ x ] -[1+ y ] = cong (λ n → -[1+ ℕ.succ n ]) (ℕ.comm-+ x y)

    assoc-+ : Associative _+_
    assoc-+ (+ x) (+ y) (+ z) = cong (λ e → + e) (ℕ.assoc-+ x y z)
    assoc-+ (+ x) (+ y) -[1+ z ] = begin
        ((x ℕ+ y) ℕ- ℕ.succ z)        ≡⟨ {!  !} ⟩
        ((+ x) + (y ℕ- ℕ.succ z)) qed
    assoc-+ (+ x) -[1+ y ] (+ z) = {!   !}
    assoc-+ (+ x) -[1+ y ] -[1+ z ] = {!   !}
    assoc-+ -[1+ x ] (+ y) (+ z) = {!   !}
    assoc-+ -[1+ x ] (+ y) -[1+ z ] = {!   !}
    assoc-+ -[1+ x ] -[1+ y ] (+ z) = {!   !}
    assoc-+ -[1+ x ] -[1+ y ] -[1+ z ] = begin
        -[1+ ℕ.succ (ℕ.succ ((x ℕ+ y) ℕ+ z)) ] ≡⟨ cong (λ e → -[1+ ℕ.succ (ℕ.succ e) ]) (ℕ.assoc-+ x y z) ⟩
        -[1+ ℕ.succ (ℕ.succ (x ℕ+ (y ℕ+ z))) ] ≡⟨ cong (λ e → -[1+ ℕ.succ e ]) (symm (ℕ.x+[1+y]≡[1+x]+y x (y ℕ+ z))) ⟩
        -[1+ ℕ.succ (x ℕ+ ℕ.succ (y ℕ+ z)) ] qed

    ℤ-+0-semigroup : Semigroup _+_
    ℤ-+0-semigroup = record { associative = assoc-+ }

    ℤ-+0-monoid : Monoid _+_ (+ 0)
    ℤ-+0-monoid = record
        { isSemigroup = ℤ-+0-semigroup
        ; identity = record { left  = 0+x≡x ; right = x+0≡x } }

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
    comm-+ (mkℤ ℕ.zero tt) (mkℤ (ℕ.succ n₁) Sign.+) = refl
    comm-+ (mkℤ ℕ.zero tt) (mkℤ (ℕ.succ n₁) Sign.-) = refl
    comm-+ (mkℤ (ℕ.succ n) Sign.+) (mkℤ ℕ.zero tt) = refl
    comm-+ (mkℤ (ℕ.succ n) Sign.+) (mkℤ (ℕ.succ n₁) Sign.+) = {!   !}
    comm-+ (mkℤ (ℕ.succ n) Sign.+) (mkℤ (ℕ.succ n₁) Sign.-) = {!   !}
    comm-+ (mkℤ (ℕ.succ n) Sign.-) (mkℤ ℕ.zero tt) = refl
    comm-+ (mkℤ (ℕ.succ n) Sign.-) (mkℤ (ℕ.succ n₁) Sign.+) = {!   !}
    comm-+ (mkℤ (ℕ.succ n) Sign.-) (mkℤ (ℕ.succ n₁) Sign.-) = {!   !}
