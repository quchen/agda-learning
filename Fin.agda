module Fin where

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
