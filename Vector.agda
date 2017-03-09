module Vector where

open import Nat
open import Bool
open import Equality
open import Algebra
open import Fin

data Vec {α} (a : Set α) : ℕ → Set α where
    [] : Vec a 0
    _∷_ : ∀ {n} → (x : a) → (xs : Vec a n) → Vec a (1 + n)

-- Auto-derive!
head : ∀ {α n} {a : Set α} → Vec a (1 + n) → a
head (x ∷ _) = x

-- Auto-derive!
tail : ∀ {α n} {a : Set α} → Vec a (1 + n) → Vec a n
tail (_ ∷ xs) = xs

-- Auto-derive!
[_] : ∀ {α} {a : Set α} → a → Vec a 1
[ x ] = x ∷ []

-- Auto-derive!
_++_ : ∀ {α m n} {a : Set α} → Vec a m → Vec a n → Vec a (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

foldr : ∀ {α n} {a b : Set α} → (a → b → b) → b → Vec a n → b
foldr f z [] = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

concat : ∀ {α m n} {a : Set α} → Vec (Vec a m) n → Vec a (n * m)
concat [] = []
concat (xs ∷ xss) = xs ++ concat xss

reverse : ∀ {n} {a : Set} → Vec a n → Vec a n
reverse = reverse' []
  where
    reverse' : ∀ {m n} {a : Set} → Vec a m → Vec a n → Vec a (m + n)
    reverse' {m = m} {a = a} xs []
      = subst (λ e → Vec a e)
              (symm (x+0≡x m))
              xs
    reverse' {m = m} {n = succ n} {a = a} xs (y ∷ ys)
      = subst (λ e → Vec a e)
              (symm (x+[1+y]≡[1+x]+y m n))
              (reverse' (y ∷ xs) ys)

index : ∀ {n} {a : Set} → Fin n → Vec a n → a
index zero (x ∷ _) = x
index (succ n) (_ ∷ xs) = index n xs
