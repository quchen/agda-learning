module Fin where



open import Logic
open import Equality

open Logic.Decidable.Binary



open import Nat as Nat
    using (ℕ; zero; succ; z≤n; s≤s; _+_)

data Fin : ℕ → Set where
    zero : {n : ℕ} → Fin (succ n)
    succ : {n : ℕ} → (i : Fin n) → Fin (succ n)

toℕ : ∀ {n} → Fin n → ℕ
toℕ zero = 0
toℕ (succ x) = succ (toℕ x)

fromℕ : (n : ℕ) → Fin (succ n)
fromℕ zero = zero
fromℕ (succ n) = succ (fromℕ n)

-- »The finite x ∈ 0..n is also a finite x ∈ 0..(n+Δn).«
extendBy : ∀ {n} Δn → Fin n → Fin (n + Δn)
extendBy {zero} _ ()
extendBy {succ _} _ zero = zero
extendBy {succ _} Δn (succ fin) = succ (extendBy Δn fin)

fromℕ' : (n : ℕ) (Δn : ℕ) → Fin (succ n + Δn)
fromℕ' n Δn = extendBy Δn (fromℕ n)

module extendBy-proofs where
    extendBy-toℕ
        : ∀ {n : ℕ} Δn (fin : Fin n)
        → toℕ fin ≡ toℕ (extendBy Δn fin)
    extendBy-toℕ _ zero = refl
    extendBy-toℕ Δn (succ fin) rewrite extendBy-toℕ Δn fin = refl

    test₁ : fromℕ' 4 0 ≡ fromℕ 4
    test₁ = refl

    -- The finite 4 ∈ 0..(4+1)
    test₂ : fromℕ' 4 1 ≡ succ (succ (succ (succ zero)))
    test₂ = refl
