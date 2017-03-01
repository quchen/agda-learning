module Algebra where

open import Equality
open import Agda.Primitive

Associative : ∀ {α} {A : Set α} (_⋆_ : A → A → A) -> Set α
Associative _⋆_ = ∀ x y z → ((x ⋆ y) ⋆ z) ≡ (x ⋆ (y ⋆ z))

record Semigroup {α : _} {A : Set α} (_⋆_ : A → A → A) : Set α where
    field
        associative : Associative _⋆_

RightIdentity : ∀ {α} {A : Set α} (_⋆_ : A → A → A) (ε : A) -> Set α
RightIdentity _⋆_ ε = ∀ x → (x ⋆ ε) ≡ x

LeftIdentity : ∀ {α} {A : Set α} (_⋆_ : A → A → A) (ε : A) -> Set α
LeftIdentity _⋆_ ε = ∀ x → (ε ⋆ x) ≡ x

record Identity {α} {A : Set α} (_⋆_ : A → A → A) (ε : A) : Set α where
    field
        left  : LeftIdentity  _⋆_ ε
        right : RightIdentity _⋆_ ε

record Monoid {α} {A : Set α} (_⋆_ : A → A → A) (ε : A) : Set α where
    field
        isSemigroup : Semigroup _⋆_
        identity    : Identity  _⋆_ ε

Commutative : ∀ {α} {A : Set α} (_⋆_ : A → A → A) -> Set α
Commutative _⋆_ = ∀ x y → (x ⋆ y) ≡ (y ⋆ x)

record CommutativeMonoid {α} {A : Set α} (_⋆_ : A → A → A) (ε : A) : Set α where
    field
        isMonoid    : Monoid      _⋆_ ε
        commutative : Commutative _⋆_

record Group {α} {A : Set α} (_⋆_ : A → A → A) (ε : A) (_⁻¹ : A → A) : Set α where
    field
        isCommutativeMonoid : CommutativeMonoid _⋆_ ε
        inverse-l : (a : A) → ((a ⁻¹) ⋆ a) ≡ ε
        inverse-r : (a : A) → (a ⋆ (a ⁻¹)) ≡ ε
