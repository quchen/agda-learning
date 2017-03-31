module BankersQueue where

open import List
open import Logic

data BankersQueue {α} (A : Set α) : Set α where
    BQ : (front back : List A) → BankersQueue A

pushFront : ∀ {α} {A : Set α} → A → BankersQueue A → BankersQueue A
pushFront x (BQ front back) = BQ (x ∷ front) back

popBack : ∀ {α} {A : Set α} → BankersQueue A → A ∧ BankersQueue A ∨ ⊤
popBack (BQ [] []) = inr tt
popBack (BQ (f ∷ ront) []) with reverse ront
popBack (BQ (f ∷ _) []) | [] = inl (f , BQ [] [])
popBack (BQ (f ∷ _) []) | t ∷ nor = inl (t , BQ [] nor)
popBack (BQ front (x ∷ back)) = inl (x , BQ back back)
