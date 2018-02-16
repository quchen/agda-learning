module Bool where



open import Function
open import Logic
open import Algebra
open import Equality

open Logic.Decidable.Binary



data Bool : Set where
    true  : Bool
    false : Bool
{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

private
    uniqueness-bool : ∀ x → (x ≡ true) ∨ (x ≡ false)
    uniqueness-bool true = inl refl
    uniqueness-bool false = inr refl

not : Bool → Bool
not true = false
not false = true

not²≡id : ∀ {P} → not (not P) ≡ P
not²≡id {true} = refl
not²≡id {false} = refl

T : Bool → Set
T true  = ⊤
T false = ⊥

⌊_⌋ : ∀ {α} {P : Set α} → Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false

¬Dec : ∀ {α} {P : Set α} → Dec P → Dec (¬ P)
¬Dec (yes p) = no (λ ¬p → ¬p p)
¬Dec (no ¬p) = yes ¬p

-- Inhabited iff the proposition is true
True : ∀ {α} {P : Set α} → Dec P → Set
True p = T ⌊ p ⌋

-- Inhabited iff the proposition is false
False : ∀ {α} {P : Set α} → Dec P → Set
False ¬p = T (not ⌊ ¬p ⌋)

data So : Bool → Set where
    Oh : So true

_≟_ : Decidable {A = Bool} _≡_
true ≟ true = yes refl
true ≟ false = no (λ ())
false ≟ true = no (λ ())
false ≟ false = yes refl

ind-Bool : {C : Bool → Set} → C true → C false → (x : Bool) → C x
ind-Bool t _ true = t
ind-Bool _ f false = f

rec-Bool : {C : Set} → C → C → Bool → C
rec-Bool {C} = ind-Bool {C = const C}

private
    -- This is how I thought this had to be written
    rec-via-ind : {C : Set} → C → C → Bool → C
    rec-via-ind {C} = ind-Bool {λ _ → C}

    -- This works as well, but I don’t understand how the inference works. C
    -- isn’t equivalent to λ _ → C, after all.
    rec-via-ind₂ : {C : Set} → C → C → Bool → C
    rec-via-ind₂ = ind-Bool

_||_ : Bool → Bool → Bool
true || _ = true
false || x = x

commutative-monoid-|| : CommutativeMonoid _||_ false
commutative-monoid-|| = record
    { isMonoid = record
        { isSemigroup = record { assoc = assoc }
        ; identity = record { left-id = left-id ; right-id = right-id } }
    ; comm = comm }
  where
    comm : Commutative _||_
    comm true true = refl
    comm true false = refl
    comm false true = refl
    comm false false = refl

    left-id : LeftIdentity _||_ false
    left-id _ = refl

    right-id : RightIdentity _||_ false
    right-id x rewrite comm x false = refl

    assoc : Associative _||_
    assoc true y z = refl
    assoc false y z = refl

_&&_ : Bool → Bool → Bool
true && x = x
false && _ = false

commutative-monoid-&& : CommutativeMonoid _&&_ true
commutative-monoid-&& = record
    { isMonoid = record
        { isSemigroup = record { assoc = assoc }
        ; identity = record { left-id = left-id ; right-id = right-id } }
    ; comm = comm }
  where
    comm : Commutative _&&_
    comm true true = refl
    comm true false = refl
    comm false true = refl
    comm false false = refl

    left-id : LeftIdentity _&&_ true
    left-id _ = refl

    right-id : RightIdentity _&&_ true
    right-id x rewrite comm x true = refl

    assoc : Associative _&&_
    assoc true y z = refl
    assoc false y z = refl

_⊕_ : Bool → Bool → Bool
true ⊕ true = false
true ⊕ false = true
false ⊕ true = true
false ⊕ false = false

group-⊕ : AbelianGroup _⊕_ false (λ x → false ⊕ x)
group-⊕ = record
    { isGroup = record
        { isMonoid = record
            { isSemigroup = record
                { assoc = assoc }
            ; identity = record
                { left-id = left-id
                ; right-id = right-id } }
        ; inverse-l = inverse-l ; inverse-r = inverse-r }
    ; comm = comm }
  where
    right-id : RightIdentity _⊕_ false
    right-id true = refl
    right-id false = refl

    left-id : LeftIdentity _⊕_ false
    left-id true = refl
    left-id false = refl

    comm : Commutative _⊕_
    comm true true = refl
    comm true false = refl
    comm false true = refl
    comm false false = refl

    -- Urgh.
    assoc : Associative _⊕_
    assoc true true true = refl
    assoc true true false = refl
    assoc true false true = refl
    assoc true false false = refl
    assoc false true true = refl
    assoc false true false = refl
    assoc false false true = refl
    assoc false false false = refl

    inverse-l : LeftInverse _⊕_ false (λ x → false ⊕ x)
    inverse-l true = refl
    inverse-l false = refl

    inverse-r : RightInverse _⊕_ false (λ x → false ⊕ x)
    inverse-r true = refl
    inverse-r false = refl
