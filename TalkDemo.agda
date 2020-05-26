open import Vector hiding (take; replicate; zipWith; transpose)
open import Nat

Type = Set

take
    : {len : ℕ} {A : Type}
    → (n : ℕ)
    → (xs : Vec A len)
    → Vec A (min len n)
take zero [] = []
take zero (x ∷ xs) = []
take (succ n) [] = []
take (succ n) (x ∷ xs) = {!   !}

zipWith
    : {n : ℕ} {a b c : Type}
    → (f  : a → b → c)
    → (xs : Vec a n)
    → (ys : Vec b n)
    → Vec c n
zipWith f [] [] = []
zipWith f (x ∷ xs) (x₁ ∷ ys) = f x x₁ ∷ zipWith f xs ys

replicate
    : {a : Type}
    → (n : ℕ)
    → (x : a)
    → Vec a n
replicate zero x = []
replicate (succ n) x = x ∷ replicate n x

Matrix : ∀ a m n → Set
Matrix a m n = Vec (Vec a m) n

transpose
    : {i j : ℕ} {a : Type}
    → Matrix a i j
    → Matrix a j i
transpose [] = replicate _ []
transpose (x ∷ x₁) = zipWith _∷_ x (transpose x₁)
