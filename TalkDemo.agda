open import Vector hiding (take)
open import Nat
open import Logic
open import Equality

data Bool : Set where
    True : Bool
    False : Bool

_&&_ : Bool → Bool → Bool
True && True = {!   !}
True && False = {!   !}
False && True = {!   !}
False && False = {!   !}

-- (∀ A. ¬¬A ⇒ A) ⇒ (∀ B. B ∨ ¬ B)
∀DNE⇒∀LEM : (∀ {α} {A : Set α} → ¬ ¬ A → A) → (∀ {β} {B : Set β} → (B ∨ ¬ B))
∀DNE⇒∀LEM = λ z {β} {B} → z (λ z₁ → z₁ (inr (λ x → z₁ (inl x))))

-- take the first (n) elements of a list (xs)
take
    : ∀ {α} {l : ℕ} {A : Set α}

      (n : ℕ)
    → (xs : Vec A l)
    → Vec A (min l n)
take = {!   !}
