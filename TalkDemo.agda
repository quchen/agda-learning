open import Vector hiding (take)
open import Nat
open import Logic

-- take the first (n) elements of a list (xs)
take
    : ∀ {α} {l : ℕ} {A : Set α}
      (n : ℕ)
    → (xs : Vec A l)
    → Vec A (min l n)
take = {!   !}
