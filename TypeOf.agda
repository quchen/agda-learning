module TypeOf where

-- Useful to use the type of one expression in another.
-- foo : TypeOf bar
TypeOf : ∀ {α} {A : Set α} → A → Set α
TypeOf {A = A} _ = A
