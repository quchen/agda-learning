module List where



open import Nat
open import Bool
open import Equality
open import Logic
open Equality.≡-Reasoning



data List {α} (a : Set α) : Set α where
    [] : List a
    _∷_ : (x : a) → (xs : List a) → List a

foldr : ∀ {α β} {a : Set α} {b : Set β} → b → (a → b → b) → List a → b
foldr z f [] = z
foldr z f (x ∷ xs) = f x (foldr z f xs)

[_] : ∀ {α} {a : Set α} → a → List a
[ x ] = x ∷ []

_++_ : ∀ {α} {a : Set α} → List a → List a → List a
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : ∀ {α} {a : Set α} → List a → ℕ
length [] = 0
length (_ ∷ xs) = 1 + length xs

length[xs++ys]≡length[xs]+length[ys]
    : ∀ {α} {a : Set α} (xs ys : List a)
    → length (xs ++ ys) ≡ length xs + length ys
length[xs++ys]≡length[xs]+length[ys] [] ys = refl
length[xs++ys]≡length[xs]+length[ys] (x ∷ xs) ys = cong succ (length[xs++ys]≡length[xs]+length[ys] xs ys)

length[xs++ys]≡length[ys++xs]
    : ∀ {α} {a : Set α} (xs ys : List a)
    → length (xs ++ ys) ≡ length (ys ++ xs)
length[xs++ys]≡length[ys++xs] xs ys =
    begin
        length (xs ++ ys)
    ≡⟨ length[xs++ys]≡length[xs]+length[ys] xs ys ⟩
        length xs + length ys
    ≡⟨ comm-+ (length xs) (length ys) ⟩
        length ys + length xs
    ≡⟨ symm (length[xs++ys]≡length[xs]+length[ys] ys xs) ⟩
        length (ys ++ xs)
    qed

-- Computationally inefficient, but easy for theorem proving :-)
reverse : ∀ {α} {a : Set α} → List a → List a
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

module reverse-equivalence where

    -- The usual linear reverse implementation
    reverse' : ∀ {α} {a : Set α} → List a → List a
    reverse' = go []
      where
        go : ∀ {α} {a : Set α} → List a → List a → List a
        go xs [] = xs
        go xs (y ∷ ys) = go (y ∷ xs) ys

    reverse[xs]≡reverse'[xs]
        : ∀ {α} {a : Set α} (xs : List a)
        → reverse xs ≡ reverse' xs
    reverse[xs]≡reverse'[xs] [] = refl
    reverse[xs]≡reverse'[xs] (x ∷ xs) = {!   !}

length[reverse[xs]]≡length[xs]
    : ∀ {α} {a : Set α} (xs : List a)
    → length (reverse xs) ≡ length xs
length[reverse[xs]]≡length[xs] [] = refl
length[reverse[xs]]≡length[xs] (x ∷ xs) =
    begin
        length (reverse xs ++ (x ∷ []))
    ≡⟨ length[xs++ys]≡length[xs]+length[ys] (reverse xs) [ x ] ⟩
        length (reverse xs) + length [ x ]
    ≡⟨ refl ⟩
        length (reverse xs) + 1
    ≡⟨ comm-+ (length (reverse xs)) 1 ⟩
        1 + length (reverse xs)
    ≡⟨ cong succ (length[reverse[xs]]≡length[xs] xs) ⟩
        succ (length xs)
    qed

reverse[reverse[xs]]≡xs
    : ∀ {α} {a : Set α} (xs : List a)
    → reverse (reverse xs) ≡ xs
reverse[reverse[xs]]≡xs [] = refl
reverse[reverse[xs]]≡xs (x ∷ xs) = {!   !}

map
    : ∀ {α β} {a : Set α} {b : Set β}
    → (f : a → b) → (xs : List a) → List b
map _ [] = []
map f (x ∷ xs) = f x ∷ map f xs

length[map[f][xs]]≡length[xs]
    : ∀ {α β} {a : Set α} {b : Set β} (f : a → b) (xs : List a)
    → length (map f xs) ≡ length xs
length[map[f][xs]]≡length[xs] _ [] = refl
length[map[f][xs]]≡length[xs] f (x ∷ xs) = cong succ (length[map[f][xs]]≡length[xs] f xs)

take
    : ∀ {α} {a : Set α}
    → ℕ → List a → List a
take zero _ = []
take _ [] = []
take (succ n) (x ∷ xs) = x ∷ take n xs

drop
    : ∀ {α} {a : Set α}
    → ℕ → List a → List a
drop zero xs = xs
drop _ [] = []
drop (succ n) (x ∷ xs) = drop n xs

splitAt
    : ∀ {a : Set}
    → ℕ → List a → List a ∧ List a
splitAt zero ys = ⟨ [] , ys ⟩
splitAt n [] = ⟨ [] , [] ⟩
splitAt (succ n) (x ∷ xs) with splitAt n xs
splitAt (succ n) (x ∷ _) | ⟨ ys , zs ⟩ = ⟨ x ∷ ys , zs ⟩

module splitAt-take-drop where

    splitAt-keeps-all-elements
        : ∀ {a : Set}
        → (n : ℕ) → (xs : List a)
        → length (proj₁ (splitAt n xs)) + length (proj₂ (splitAt n xs)) ≡ length xs
    splitAt-keeps-all-elements n xs = {!   !}

    splitAt[xs]≡⟨take[xs],drop[xs]⟩
        : ∀ {a : Set}
        → (n : ℕ) → (xs : List a)
        → splitAt n xs ≡ ⟨ take n xs , drop n xs ⟩
    splitAt[xs]≡⟨take[xs],drop[xs]⟩ zero [] = refl
    splitAt[xs]≡⟨take[xs],drop[xs]⟩ zero (x ∷ xs) = refl
    splitAt[xs]≡⟨take[xs],drop[xs]⟩ (succ n) [] = refl
    splitAt[xs]≡⟨take[xs],drop[xs]⟩ (succ n) (x ∷ xs) = {!   !}
