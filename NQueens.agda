-- This is a rewrite of the N-Queens blogpost
-- https://aphyr.com/posts/342-typing-the-technical-interview
-- in Agda.

module NQueens where

data List A : Set where
    [] : List A
    _∷_ : (x : A) → (xs : List A) → List A

-- »listConcat« in the blogpost
_++_ : ∀ {A} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

listConcatAll : ∀ {A} → List (List A) → List A
listConcatAll [] = []
listConcatAll (xs ∷ xss) = xs ++ listConcatAll xss

module Bool where
    data Bool : Set where
        true : Bool
        false : Bool

    not : Bool → Bool
    not true = false
    not false = true

    infixr 20 _or_
    _or_ : Bool → Bool → Bool
    true or _ = true
    false or y = y

open Bool

module Nat where
    data ℕ : Set where
        zero : ℕ
        succ : (n : ℕ) → ℕ
    -- To recover nice notation like 3 instead of succ (succ (succ zero))
    {-# BUILTIN NATURAL ℕ #-}

    -- »PeanoEqual« in the post
    _≟_ : ℕ → ℕ → Bool
    zero ≟ zero = true
    succ x ≟ succ y = x ≟ y
    _ ≟ _ = false

    -- »PeanoLT« in the post
    _<_ : ℕ → ℕ → Bool
    zero < zero = false
    zero < succ y = true
    succ x < zero = false
    succ x < succ y = x < y

    absDiff : ℕ → ℕ → ℕ
    absDiff zero n = n
    absDiff n zero = n
    absDiff (succ n₁) (succ n₂) = absDiff n₁ n₂

open Nat


range : ℕ → List ℕ
range zero = []
range (succ n) = succ n ∷ range n

map : ∀ {A B} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

mapCat : ∀ {A B} → (A → List B) → List A → List B
mapCat f xs = listConcatAll (map f xs)

anyTrue : List Bool → Bool
anyTrue [] = false
anyTrue (x ∷ xs) = x or anyTrue xs

filter : ∀ {A} → (A → Bool) → List A → List A
filter _ [] = []
filter p (x ∷ xs) with p x
… | true = x ∷ filter p xs
… | false = filter p xs

data Queen : Set where
    queen : (x : ℕ) → (y : ℕ) → Queen

Configuration : Set
Configuration = List Queen

queensInRow : ℕ → ℕ → List Queen
queensInRow n x = map (queen x) (range n)

threatens : Queen → Queen → Bool
threatens (queen x₁ y₁) (queen x₂ y₂)
  = (absDiff x₁ x₂ ≟ absDiff y₁ y₂) or (x₁ ≟ x₂) or (y₁ ≟ y₂)

safeToAdd : Configuration → Queen → Bool
safeToAdd qs q = not (anyTrue (map (threatens q) qs))

-- Add a queen to an n×n chess board in the x-th row, for all n positions in
-- that row. Return all working configurations.
addQueen : ℕ → ℕ → Configuration → List (Configuration)
addQueen n x c = map (λ q → q ∷ c) (filter (safeToAdd c) (queensInRow n x))

addQueenToAll : ℕ → ℕ → List Configuration → List Configuration
addQueenToAll n x = mapCat (addQueen n x)

addQueens2 : ℕ → ℕ → List Configuration → List Configuration
addQueens2 n x cs = {!   !}

{-# TERMINATING #-}
mutual
    addQueensIf : Bool → ℕ → ℕ → List Configuration → List Configuration
    addQueensIf false _ _ cs = cs
    addQueensIf true n x cs = addQueens n (succ x) (addQueenToAll n x cs)

    addQueens : ℕ → ℕ → List Configuration → List Configuration
    addQueens n x cs = addQueensIf (x < n) n x cs

nQueens : ℕ → List Configuration
nQueens n = addQueens n zero ([] ∷ [])

data Solution : Configuration → Set where
    validConfiguration : ∀ c → Solution c

data Unsolvable : Set where

solve : List Configuration → Set
solve [] = Unsolvable
solve (c ∷ _) = Solution c

solution : solve (nQueens 6)
solution = validConfiguration _
