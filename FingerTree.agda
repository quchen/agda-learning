module FingerTree where

open import Algebra
open import List hiding (foldr)
open import Equality
open import Fin
open import Function
open import Logic
open import Nat
open import Vector hiding (_++_; foldr; toList)

-- Vectors of length 0..n
Vec≤ : ∀ {α} → Set α → ℕ → Set α
Vec≤ A l = Σ (Fin (succ l)) (Vec A ∘ toℕ)

infixr 6 _◁_
infixr 6 _◁◁_
infixl 6 _▷_
infixl 6 _▷▷_
infixr 5 _⋈_

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

_◁_ : ∀ {α} {A : Set α} → (x : A) → (xs : FingerTree23 A) → FingerTree23 A
x ◁ Empty = Single x
x ◁ Single y = Deep (Digit1 x) Empty (Digit1 y)
x ◁ Deep (Digit1 d₁)          xs rd = Deep (Digit2 x d₁)       xs                    rd
x ◁ Deep (Digit2 d₁ d₂)       xs rd = Deep (Digit3 x d₁ d₂)    xs                    rd
x ◁ Deep (Digit3 d₁ d₂ d₃)    xs rd = Deep (Digit4 x d₁ d₂ d₃) xs                    rd
x ◁ Deep (Digit4 d₁ d₂ d₃ d₄) xs rd = Deep (Digit2 x d₁)       (Node3 d₂ d₃ d₄ ◁ xs) rd

data ViewL {α} (A : Set α) (B : Set α → Set α) : Set α where
    EmptyL : ViewL A B
    _◁∷_ : (x : A) → (xs : B A) → ViewL A B

viewL : ∀ {α} {A : Set α} → FingerTree23 A → ViewL A FingerTree23
viewL Empty = EmptyL
viewL (Single x) = x ◁∷ Empty
viewL (Deep (Digit1 _) deep _)                 with viewL deep
viewL (Deep (Digit1 x) _ (Digit1 d₁))          | EmptyL               = x ◁∷ Single d₁
viewL (Deep (Digit1 x) _ (Digit2 d₁ d₂))       | EmptyL               = x ◁∷ Deep (Digit1 d₁) Empty (Digit1 d₂)
viewL (Deep (Digit1 x) _ (Digit3 d₁ d₂ d₃))    | EmptyL               = x ◁∷ Deep (Digit1 d₁) Empty (Digit2 d₂ d₃)
viewL (Deep (Digit1 x) _ (Digit4 d₁ d₂ d₃ d₄)) | EmptyL               = x ◁∷ Deep (Digit1 d₁) Empty (Digit3 d₂ d₃ d₄)
viewL (Deep (Digit1 x) _ dr)                   | Node2 n₁ n₂ ◁∷ xs    = x ◁∷ Deep (Digit2 n₁ n₂) xs dr
viewL (Deep (Digit1 x) _ dr)                   | Node3 n₁ n₂ n₃ ◁∷ xs = x ◁∷ Deep (Digit3 n₁ n₂ n₃) xs dr
viewL (Deep (Digit2 x x₁) x₂ rd)       = x ◁∷ Deep (Digit1 x₁)       x₂ rd
viewL (Deep (Digit3 x x₁ x₂) x₃ rd)    = x ◁∷ Deep (Digit2 x₁ x₂)    x₃ rd
viewL (Deep (Digit4 x x₁ x₂ x₃) x₄ rd) = x ◁∷ Deep (Digit3 x₁ x₂ x₃) x₄ rd

_◁◁_ : ∀ {α} {A : Set α} → (ds : Digit A) → (xs : FingerTree23 A) → FingerTree23 A
Digit1 x₁          ◁◁ xs = x₁ ◁ xs
Digit2 x₁ x₂       ◁◁ xs = x₁ ◁ x₂ ◁ xs
Digit3 x₁ x₂ x₃    ◁◁ xs = x₁ ◁ x₂ ◁ x₃ ◁ xs
Digit4 x₁ x₂ x₃ x₄ ◁◁ xs = x₁ ◁ x₂ ◁ x₃ ◁ x₄ ◁ xs

_▷_ : ∀ {α} {A : Set α} → (xs : FingerTree23 A) → (x : A) → FingerTree23 A
Empty ▷ x = Single x
Single x ▷ y = Deep (Digit1 x) Empty (Digit1 y)
Deep ld xs (Digit1 d₁)          ▷ x = Deep ld xs                    (Digit2 d₁ x)
Deep ld xs (Digit2 d₁ d₂)       ▷ x = Deep ld xs                    (Digit3 d₁ d₂ x)
Deep ld xs (Digit3 d₁ d₂ d₃)    ▷ x = Deep ld xs                    (Digit4 d₁ d₂ d₃ x)
Deep ld xs (Digit4 d₁ d₂ d₃ d₄) ▷ x = Deep ld (xs ▷ Node3 d₁ d₂ d₃) (Digit2 d₄ x)

data ViewR {α} (A : Set α) (B : Set α → Set α) : Set α where
    EmptyR : ViewR A B
    _∷▷_ : (xs : B A) → (x : A) → ViewR A B

viewR : ∀ {α} {A : Set α} → FingerTree23 A → ViewR A FingerTree23
viewR Empty = EmptyR
viewR (Single x) = Empty ∷▷ x
viewR (Deep _ deep (Digit1 _))                 with viewR deep
viewR (Deep (Digit1 d₁)          _ (Digit1 x)) | EmptyR = Single d₁ ∷▷ x
viewR (Deep (Digit2 d₁ d₂)       _ (Digit1 x)) | EmptyR = Deep (Digit1 d₁) Empty (Digit1 d₂) ∷▷ x
viewR (Deep (Digit3 d₁ d₂ d₃)    _ (Digit1 x)) | EmptyR = Deep (Digit2 d₁ d₂) Empty (Digit1 d₃) ∷▷ x
viewR (Deep (Digit4 d₁ d₂ d₃ d₄) _ (Digit1 x)) | EmptyR = Deep (Digit3 d₁ d₂ d₃) Empty (Digit1 d₄) ∷▷ x
viewR (Deep ld                   _ (Digit1 x)) | xs ∷▷ Node2 n₁ n₂ = Deep ld xs (Digit2 n₁ n₂) ∷▷ x
viewR (Deep ld                   _ (Digit1 x)) | xs ∷▷ Node3 n₁ n₂ n₃ = Deep ld xs (Digit3 n₁ n₂ n₃) ∷▷ x
viewR (Deep ld deep (Digit2 d₁ x))       = Deep ld deep (Digit1 d₁)       ∷▷ x
viewR (Deep ld deep (Digit3 d₂ d₁ x))    = Deep ld deep (Digit2 d₂ d₁)    ∷▷ x
viewR (Deep ld deep (Digit4 d₃ d₂ d₁ x)) = Deep ld deep (Digit3 d₃ d₂ d₁) ∷▷ x

_▷▷_ : ∀ {α} {A : Set α} → (xs : FingerTree23 A) → (ds : Digit A) → FingerTree23 A
xs ▷▷ Digit1 x₁ = xs ▷ x₁
xs ▷▷ Digit2 x₁ x₂ = xs ▷ x₁ ▷ x₂
xs ▷▷ Digit3 x₁ x₂ x₃ = xs ▷ x₁ ▷ x₂ ▷ x₃
xs ▷▷ Digit4 x₁ x₂ x₃ x₄ = xs ▷ x₁ ▷ x₂ ▷ x₃ ▷ x₄

-- ⋈ = \bowtie
_⋈_ : ∀ {α} {A : Set α} → (xs : FingerTree23 A) → (ys : FingerTree23 A) → FingerTree23 A
Empty ⋈ ys = ys
Single x ⋈ ys = x ◁ ys
xs ⋈ Empty = xs
xs ⋈ Single x = xs ▷ x
Deep xld xs (Digit1 lx₁)           ⋈ Deep (Digit1 rx₁)             ys yrd = Deep xld {!   !} yrd
Deep xld xs (Digit1 lx₁)           ⋈ Deep (Digit2 rx₁ rx₂)         ys yrd = Deep xld {!   !} yrd
Deep xld xs (Digit1 lx₁)           ⋈ Deep (Digit3 rx₁ rx₂ rx₃)     ys yrd = Deep xld {!   !} yrd
Deep xld xs (Digit1 lx₁)           ⋈ Deep (Digit4 rx₁ rx₂ rx₃ rx₄) ys yrd = Deep xld {!   !} yrd
Deep xld xs (Digit2 lx₁ lx₂)       ⋈ Deep (Digit1 rx₁)             ys yrd = Deep xld {!   !} yrd
Deep xld xs (Digit2 lx₁ lx₂)       ⋈ Deep (Digit2 rx₁ rx₂)         ys yrd = Deep xld {!   !} yrd
Deep xld xs (Digit2 lx₁ lx₂)       ⋈ Deep (Digit3 rx₁ rx₂ rx₃)     ys yrd = Deep xld {!   !} yrd
Deep xld xs (Digit2 lx₁ lx₂)       ⋈ Deep (Digit4 rx₁ rx₂ rx₃ rx₄) ys yrd = Deep xld {!   !} yrd
Deep xld xs (Digit3 lx₁ lx₂ x₃)    ⋈ Deep (Digit1 rx₁)             ys yrd = Deep xld {!   !} yrd
Deep xld xs (Digit3 lx₁ lx₂ x₃)    ⋈ Deep (Digit2 rx₁ rx₂)         ys yrd = Deep xld {!   !} yrd
Deep xld xs (Digit3 lx₁ lx₂ x₃)    ⋈ Deep (Digit3 rx₁ rx₂ rx₃)     ys yrd = Deep xld {!   !} yrd
Deep xld xs (Digit3 lx₁ lx₂ x₃)    ⋈ Deep (Digit4 rx₁ rx₂ rx₃ rx₄) ys yrd = Deep xld {!   !} yrd
Deep xld xs (Digit4 lx₁ lx₂ x₃ x₄) ⋈ Deep (Digit1 rx₁)             ys yrd = Deep xld {!   !} yrd
Deep xld xs (Digit4 lx₁ lx₂ x₃ x₄) ⋈ Deep (Digit2 rx₁ rx₂)         ys yrd = Deep xld {!   !} yrd
Deep xld xs (Digit4 lx₁ lx₂ x₃ x₄) ⋈ Deep (Digit3 rx₁ rx₂ rx₃)     ys yrd = Deep xld {!   !} yrd
Deep xld xs (Digit4 lx₁ lx₂ x₃ x₄) ⋈ Deep (Digit4 rx₁ rx₂ rx₃ rx₄) ys yrd = Deep xld {!   !} yrd

module Induction where
    ind-FingerTree23
        : ∀ {α γ} {A : Set α} {C : FingerTree23 A → Set γ}
        → (empty : C Empty)
        → (single : (x : A) → C (Single x))
        → (deep : (d← : Digit A) → (xs : FingerTree23 (Node A)) → (d→ : Digit A) → C (Deep d← xs d→))
        → (xs : FingerTree23 A)
        → C xs
    ind-FingerTree23 empty _      _ Empty         = empty
    ind-FingerTree23 _     single _ (Single x)    = single x
    ind-FingerTree23 _     _ deep (Deep ld xs rd) = deep ld xs rd

    ind-Digit
        : ∀ {α γ} {A : Set α} {C : Digit A → Set γ}
        → (digit1 : (x₁ : A) → C (Digit1 x₁))
        → (digit2 : (x₁ x₂ : A) → C (Digit2 x₁ x₂))
        → (digit3 : (x₁ x₂ x₃ : A) → C (Digit3 x₁ x₂ x₃))
        → (digit4 : (x₁ x₂ x₃ x₄ : A) → C (Digit4 x₁ x₂ x₃ x₄))
        → (d : Digit A)
        → C d
    ind-Digit digit1 _ _ _ (Digit1 x₁)          = digit1 x₁
    ind-Digit _ digit2 _ _ (Digit2 x₁ x₂)       = digit2 x₁ x₂
    ind-Digit _ _ digit3 _ (Digit3 x₁ x₂ x₃)    = digit3 x₁ x₂ x₃
    ind-Digit _ _ _ digit4 (Digit4 x₁ x₂ x₃ x₄) = digit4 x₁ x₂ x₃ x₄

    ind-Node
        : ∀ {α γ} {A : Set α} {C : Node A → Set γ}
        → (node2 : (x₁ x₂ : A) → C (Node2 x₁ x₂))
        → (node3 : (x₁ x₂ x₃ : A) → C (Node3 x₁ x₂ x₃))
        → (d : Node A)
        → C d
    ind-Node node2 _ (Node2 x₁ x₂)    = node2 x₁ x₂
    ind-Node _ node3 (Node3 x₁ x₂ x₃) = node3 x₁ x₂ x₃

    rec-FingerTree23
        : ∀ {α γ} {A : Set α} {C : Set γ}
        → (empty : C)
        → (single : A → C)
        → (deep : Digit A → FingerTree23 (Node A) → Digit A → C)
        → FingerTree23 A
        → C
    rec-FingerTree23 = ind-FingerTree23

toList : ∀ {α} {A : Set α} → FingerTree23 A → List A
toList Empty = []
toList (Single x) = x ∷ []
toList (Deep ld xs rd) = {!   !}
