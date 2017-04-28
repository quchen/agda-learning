module Termination where

open import Algebra
open import Agda.Primitive

-- Reachability: Acc _≺_ x means that all y ≺ x can be reached via chaining the
-- relation. For example, Accessible < 3 because 0 < 1 < 2 < 3.
--
-- Taken from the Agda standard library, minus the obfuscation.
data Accessible {α ρ} {A : Set α} (_≺_ : Rel A ρ) (x : A) : Set (α ⊔ ρ) where
    acc : (∀ y → y ≺ x → Accessible _≺_ y) → Accessible _≺_ x

WellFounded : ∀ {α ρ} {A : Set α} → Rel A ρ → Set _
WellFounded _≺_ = ∀ x → Accessible _≺_ x

-- -- Termination proof based on mapping a relation to a well-founded relation.
-- module measured
--     {α ρA} {A : Set α} (_≺A_ : Rel A ρA)
--     {β ρB} {B : Set β} (_≺B_ : Rel B ρB)
--   where
--
--     measured
--         : (f : B → A)
--         → (decrese : ∀ {b₁ b₂} → b₁ ≺B b₂ → f b₁ ≺A f b₂)
--         → WellFounded _≺A_ → WellFounded _≺B_
--     measured f decrese x x₁ = acc h
--       where
--         h : (x₂ : B) (x₃ : x₂ ≺B x₁) → Accessible _≺B_ x₂
--         h = {!   !}
