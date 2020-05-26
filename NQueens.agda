-- A solution of the N-Queens-Problem in Agda.
-- Completely standalone.

module NQueens where

data List A : Set where
    [] : List A
    _∷_ : (x : A) → (xs : List A) → List A

-- »listConcat« in the blogpost
_++_ : ∀ {A} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- »listConcatAll« in the post
concat : ∀ {A} → List (List A) → List A
concat [] = []
concat (xs ∷ xss) = xs ++ concat xss

module Bool where
    data Bool : Set where
        true : Bool
        false : Bool

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

    _≟_ : ℕ → ℕ → Bool
    zero ≟ zero = true
    succ x ≟ succ y = x ≟ y
    _ ≟ _ = false

    ∣_-_∣ : ℕ → ℕ → ℕ
    ∣ zero - n₂ ∣ = n₂
    ∣ n₁ - zero ∣ = n₁
    ∣ succ n₁ - succ n₂ ∣ = ∣ n₁ - n₂ ∣

open Nat

module Fin where
    data Fin : ℕ → Set where
        fzero : {n : ℕ} → Fin (succ n)
        fsucc : {n : ℕ} → (i : Fin n) → Fin (succ n)

    toℕ : ∀ {n} → Fin n → ℕ
    toℕ fzero = 0
    toℕ (fsucc n) = succ (toℕ n)

    fromℕ : ∀ n → Fin (succ n)
    fromℕ zero = fzero
    fromℕ (succ n) = fsucc (fromℕ n)

    raise : ∀ {n} → Fin n → Fin (succ n)
    raise fzero = fzero
    raise (fsucc x) = fsucc (raise x)

open Fin

map : ∀ {A B} → (A → B) → List A → List B
map _ [] = []
map f (x ∷ xs) = f x ∷ map f xs

range2 : (n : ℕ) → List (Fin (succ n))
range2 zero = fzero ∷ []
range2 (succ n) = fromℕ (succ n) ∷ map raise (range2 n)

range : (n : ℕ) → List (Fin (succ n))
range zero = []
range (succ n) = fzero ∷ map fsucc (range n)

-- »catMap« in the post
concatMap : ∀ {A B} → (A → List B) → List A → List B
concatMap f xs = concat (map f xs)

filter : ∀ {A} → (A → Bool) → List A → List A
filter _ [] = []
filter p (x ∷ xs) with p x
… | true = x ∷ filter p xs
… | false = filter p xs

none : ∀ {A} → (A → Bool) → List A → Bool
none p xs with filter p xs
… | [] = true
… | _  = false

-- »Queen n« is a queen on an n×n chess board.
data Queen : ℕ → Set where
    queen : ∀ {n} (x y : Fin (succ n)) → Queen (succ n)

Configuration : ℕ → Set
Configuration n = List (Queen n)

queensInRow : {n : ℕ} → Fin (succ n) → List (Queen (succ n))
queensInRow {n} x = map (queen x) (range n)

threatens : ∀ {n} → Queen (succ n) → Queen (succ n) → Bool
threatens (queen x₁ y₁) (queen x₂ y₂) = (Δx ≟ 0) or (Δy ≟ 0) or (Δx ≟ Δy)
  where
    Δx = ∣ toℕ x₁ - toℕ x₂ ∣
    Δy = ∣ toℕ y₁ - toℕ y₂ ∣

safeToAdd : ∀ {n} → Configuration (succ n) → Queen (succ n) → Bool
safeToAdd c q = none (threatens q) c

-- Add a queen to an n×n chess board in the x-th row, for all n column positions
-- in that row. Return all working configurations.
addQueenToRow : ∀ {n} → (row : Fin (succ n)) → Configuration (succ n) → List (Configuration (succ n))
addQueenToRow x c = map (λ q → q ∷ c) (filter (safeToAdd c) (queensInRow x))

addQueensToRow : ∀ {n} → (row : Fin (succ n)) → List (Configuration (succ n)) → List (Configuration (succ n))
addQueensToRow x = concatMap (addQueenToRow x)

addAllQueensToRows : ∀ {n} → (rows : List (Fin (succ n))) → List (Configuration (succ n)) → List (Configuration (succ n))
addAllQueensToRows [] c = c
addAllQueensToRows (row ∷ rs) c = addAllQueensToRows rs (addQueensToRow row c)

data Solution : ∀ {n} → Configuration (succ n) → Set where
    validConfiguration : ∀ {n} (c : Configuration (succ n)) → Solution c

data Unsolvable : Set where

NQueens : ℕ → Set
NQueens n with addAllQueensToRows (range n) ([] ∷ [])
… | [] = Unsolvable
… | c ∷ _ = Solution c

solution : NQueens 4
solution = {!   !}
