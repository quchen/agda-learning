module Stream where



open import Logic
open import Nat
open import Function
open import Equality



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

iterate : ∀ {α} {A : Set α} → (A → A) → A → Stream A
head (iterate f x) = x
tail (iterate f x) = x ∷ iterate f (f x)

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

_‼_ : ∀ {α} {A : Set α} → Stream A → ℕ → A
x ‼ zero = head x
x ‼ succ n = tail x ‼ n

private
    repeat-‼ : ∀ {α} {A : Set α} {x : A} n → repeat x ‼ n ≡ x
    repeat-‼ zero = refl
    repeat-‼ (succ n) = repeat-‼ n

    repeat-iterate-const
        : ∀ {α} {A : Set α}
        → (x y : A)
        → iterate (const x) y ≡ repeat x
    repeat-iterate-const x y = {!   !}

    repeat-iterate-id
        : ∀ {α} {A : Set α}
        → (x : A)
        → iterate id x ≡ repeat x
    repeat-iterate-id x = {! x  !}


-- fibs : Stream ℕ
-- head fibs = 0
-- head (tail fibs) = 1
-- tail (tail fibs) = zipWith _+_ fibs (tail fibs)
