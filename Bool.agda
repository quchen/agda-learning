module Bool where



open import Logic
open import Equality

open Logic.Decidable.Binary



data Bool : Set where
    true  : Bool
    false : Bool

not : Bool -> Bool
not true = false
not false = true

not²≡id : ∀ {P} → not (not P) ≡ P
not²≡id {true} = refl
not²≡id {false} = refl

T : Bool → Set
T true  = ⊤
T false = ⊥

⌊_⌋ : ∀ {α} {P : Set α} → Dec P → Bool
⌊ yes x ⌋ = true
⌊ no  x ⌋ = false

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
