module Vector where

open import Nat
open import Equality
open import Algebra
open import Bool
open import Logic
import List as 𝕃
open import Fin
open import Function
open Equality.≡-Reasoning

infixr 6 _∷_
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

-- Nicely auto-derivable :-)
take : ∀ {α} {a : ℕ} {A : Set α} b → Vec A a → Vec A (a ⊓ b)
take zero (_ ∷ _) = []
take zero [] = []
take _ [] = []
take (succ b) (x ∷ xs) = x ∷ take b xs

-- Nicely showcases subst.
-- I wonder whether this type uniquely specifies its value.
drop : ∀ {α} {a : ℕ} {A : Set α} b → Vec A a → Vec A (a ∸ b)
drop _ [] = []
drop {a = a} {A = A} zero x = subst (Vec A) (symm (x∸0≡x a)) x -- ugh
drop (succ b) (x ∷ xs) = drop b xs

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

replicate : ∀ {n} {a : Set} → a → Vec a n
replicate {zero} _ = []
replicate {succ n} x = x ∷ replicate {n} x

-- Case split -> auto :-)
pointwiseApply : ∀ {n} {a b : Set} → Vec (a → b) n → Vec a n → Vec b n
pointwiseApply [] [] = []
pointwiseApply (f ∷ fs) (x ∷ xs) = f x ∷ pointwiseApply fs xs

-- Case split -> auto :-)
zip : ∀ {n} {a b : Set} → Vec a n → Vec b n → Vec (a ∧ b) n
zip [] [] = []
zip (x ∷ xs) (y ∷ ys) = ⟨ x , y ⟩ ∷ zip xs ys

-- Case split -> auto :-)
zipWith : ∀ {n} {a b c : Set} → (a → b → c) → Vec a n → Vec b n → Vec c n
zipWith f [] [] = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

tabulate : ∀ {n} {a : Set} → (Fin n → a) → Vec a n
tabulate {zero} f = []
tabulate {succ n} f = f zero ∷ tabulate (f ∘ succ)

module tabulate-test where
    square : ∀ {n} → Fin n → ℕ
    square = (λ n → n * n) ∘ toℕ

    test₁ : tabulate square ≡ 0 ∷ 1 ∷ 4 ∷ 9 ∷ 16 ∷ 25 ∷ 36 ∷ []
    test₁ = refl

transpose : ∀ {m n} {a : Set} → Vec (Vec a m) n → Vec (Vec a n) m
transpose [] = replicate []
transpose (xs ∷ xss) = zipWith _∷_ xs (transpose xss)

module matrix-test where
    testMatrix : Vec (Vec ℕ 3) 4
    testMatrix = ((11 ∷ 12 ∷ 13 ∷ [])
                ∷ (21 ∷ 22 ∷ 23 ∷ [])
                ∷ (31 ∷ 32 ∷ 33 ∷ [])
                ∷ (41 ∷ 42 ∷ 43 ∷ []) ∷ [])

    testTranspose : transpose testMatrix
            ≡
              (11 ∷ 21 ∷ 31 ∷ 41 ∷ [])
            ∷ (12 ∷ 22 ∷ 32 ∷ 42 ∷ [])
            ∷ (13 ∷ 23 ∷ 33 ∷ 43 ∷ []) ∷ []
    testTranspose = refl

-- Auto-derivable :-)
index-is-inverse-of-tabulate
    : ∀ {n} {a : Set}
    → (f : Fin n → a) (i : Fin n) → index i (tabulate f) ≡ f i
index-is-inverse-of-tabulate f zero = refl
index-is-inverse-of-tabulate f (succ i) = index-is-inverse-of-tabulate (f ∘ succ) i

tabulate-is-inverse-of-index
    : ∀ {n} {a : Set}
    → (xs : Vec a n)
    → tabulate (λ k → index k xs) ≡ xs
tabulate-is-inverse-of-index [] = refl
tabulate-is-inverse-of-index (x ∷ xs) = cong (λ e → x ∷ e) (tabulate-is-inverse-of-index xs)

-- The pairs are autoderivable when the first component is known
filter : ∀ {α n} {A : Set α} → (A → Bool) → Vec A n → Σ ℕ (Vec A)
filter _ [] = zero , []
filter p (x ∷ xs) with p x | filter p xs
… | true  | (n , vs) = (succ n , x ∷ vs)
… | false | (n , vs) = (n , vs)

fromList : ∀ {α} {A : Set α} → 𝕃.List A → Σ ℕ (Vec A)
fromList 𝕃.[] = zero , []
fromList (x 𝕃.∷ xs) with fromList xs
fromList (x 𝕃.∷ xs) | n , vs = succ n , x ∷ vs

toList : ∀ {α n} {A : Set α} → Vec A n → 𝕃.List A
toList = foldr 𝕃._∷_ 𝕃.[]
