open import Agda.Primitive
open import Logic
open import Nat
open import Equality



-- ind-Σ
--     : ∀ {α β γ} {A : Set α} {B : A → Set β}
--     → (C : Σ A B → Set γ)
--     → ((a : A) → (b : B a) → C (a , b))
--     → (x : Σ A B)
--     → C x
-- ind-Σ C f (x , y) = f x y
