module FingerTree where

open import Fin
open import Logic
open import Nat
open import Vector hiding (_++_)
open import Function

-- Vectors of length 0..n
Vec≤ : ∀ {α} → Set α → ℕ → Set α
Vec≤ A l = Σ (Fin (succ l)) (Vec A ∘ toℕ)

module Examples where
    examples : Vec (Vec≤ ℕ 3) _
    examples = (fromℕ' 0 3 , [])
             ∷ (fromℕ' 1 2 , 1 ∷ [])
             ∷ (fromℕ' 2 1 , 1 ∷ 2 ∷ [])
             ∷ (fromℕ' 3 0 , 1 ∷ 2 ∷ 3 ∷ [])
             ∷ []

data Digit {α} (A : Set α) : Set α where
    Digit1 : A → Digit A
    Digit2 : A → A → Digit A
    Digit3 : A → A → A → Digit A
    Digit4 : A → A → A → A → Digit A

data Node {α} (A : Set α) : Set α where
    Node2 : A → A → Node A
    Node3 : A → A → A → Node A

data FingerTree23 {α} (A : Set α) : Set α where
    Empty : FingerTree23 A
    Single : (x : A) → FingerTree23 A
    Deep : (ld : Digit A) → (sub : FingerTree23 (Node A)) → (rd : Digit A) → FingerTree23 A


-- ▷ = \rhd
-- ◁ = \lhd

infixr 6 _◁_
_◁_ : ∀ {α} {A : Set α} → (x : A) → (xs : FingerTree23 A) → FingerTree23 A
x ◁ Empty = Single x
x ◁ Single y = Deep (Digit1 x) Empty (Digit1 y)
x ◁ Deep (Digit1 d₁) xs rd = Deep (Digit2 x d₁) xs rd
x ◁ Deep (Digit2 d₁ d₂) xs rd = Deep (Digit3 x d₁ d₂) xs rd
x ◁ Deep (Digit3 d₁ d₂ d₃) xs rd = Deep (Digit4 x d₁ d₂ d₃) xs rd
x ◁ Deep (Digit4 d₁ d₂ d₃ d₄) xs rd = Deep (Digit2 x d₁) (Node3 d₂ d₃ d₄ ◁ xs) rd

infixl 6 _▷_
_▷_ : ∀ {α} {A : Set α} → (xs : FingerTree23 A) → (x : A) → FingerTree23 A
Empty ▷ x = Single x
Single x ▷ y = Deep (Digit1 x) Empty (Digit1 y)
Deep ld xs (Digit1 d₁) ▷ x = Deep ld xs (Digit2 d₁ x)
Deep ld xs (Digit2 d₁ d₂) ▷ x = Deep ld xs (Digit3 d₁ d₂ x)
Deep ld xs (Digit3 d₁ d₂ d₃) ▷ x = Deep ld xs (Digit4 d₁ d₂ d₃ x)
Deep ld xs (Digit4 d₁ d₂ d₃ d₄) ▷ x = Deep ld (xs ▷ Node3 d₁ d₂ d₃) (Digit2 d₄ x)

_++_ : ∀ {α} {A : Set α} → (xs : FingerTree23 A) → (ys : FingerTree23 A) → FingerTree23 A
Empty ++ ys = ys
Single x ++ ys = x ◁ ys
xs ++ Empty = xs
xs ++ Single x = xs ▷ x
Deep xld xs xrd ++ Deep yld ys yrd = Deep xld {!   !} yrd
