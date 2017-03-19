module Fin where



open import Logic
open import Equality

open Logic.Decidable.Binary



open import Nat as Nat
    using (ℕ; zero; succ; z≤n; s≤s)

data Fin : ℕ → Set where
    zero : {n : ℕ} → Fin (succ n)
    succ : {n : ℕ} → (i : Fin n) → Fin (succ n)

toℕ : ∀ {n} → Fin n → ℕ
toℕ zero = 0
toℕ (succ x) = succ (toℕ x)

fromℕ : (n : ℕ) → Fin (succ n)
fromℕ zero = zero
fromℕ (succ n) = succ (fromℕ n)

_≟_ : ∀ {n} → Decidable {A = Fin n} _≡_
zero ≟ zero = yes refl
zero ≟ succ y = no (λ ())
succ x ≟ zero = no (λ ())
succ x ≟ succ y with x ≟ y
succ x ≟ succ .x | yes refl = yes refl
succ x ≟ succ y | no x≢y = no (λ foo → x≢y {!   !})

equality-of-successors : ∀ {n} {a b : Fin (succ n)} → succ a ≡ succ b → a ≡ b
equality-of-successors eq = {!   !}
