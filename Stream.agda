module Stream where

open import Logic

record Stream {α} (A : Set α) : Set α where
    coinductive
    constructor _∷_
    field
        head : A
        tail : Stream A

open Stream

repeat : ∀ {α} {A : Set α} → A → Stream A
head (repeat x) = x
tail (repeat x) = repeat x

zip : ∀ {α β} {A : Set α} {B : Set β} → Stream A → Stream B → Stream (A × B)
head (zip xs ys) = (head xs , head ys)
tail (zip xs ys) = zip (tail xs) (tail ys)

zipWith
    : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
    → (A → B → C) → Stream A → Stream B → Stream C
head (zipWith f xs ys) = f (head xs) (head ys)
tail (zipWith f xs ys) = zipWith f (tail xs) (tail ys)

map : ∀ {α β} {A : Set α} {B : Set β} → (A → B) → Stream A → Stream B
head (map f xs) = f (head xs)
tail (map f xs) = map f (tail xs)
