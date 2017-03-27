module Algebra where

open import Equality
open Equality.≡-Reasoning
open import Agda.Primitive

Associative : ∀ {α} {A : Set α} (_·_ : A → A → A) -> Set α
Associative _·_ = ∀ x y z → ((x · y) · z) ≡ (x · (y · z))

record Semigroup {α : _} {A : Set α} (_·_ : A → A → A) : Set α where
    field
        assoc : Associative _·_

RightIdentity : ∀ {α} {A : Set α} (_·_ : A → A → A) (ε : A) -> Set α
RightIdentity _·_ ε = ∀ x → (x · ε) ≡ x

LeftIdentity : ∀ {α} {A : Set α} (_·_ : A → A → A) (ε : A) -> Set α
LeftIdentity _·_ ε = ∀ x → (ε · x) ≡ x

record Identity {α} {A : Set α} (_·_ : A → A → A) (ε : A) : Set α where
    field
        left-id  : LeftIdentity  _·_ ε
        right-id : RightIdentity _·_ ε

record Monoid {α} {A : Set α} (_·_ : A → A → A) (ε : A) : Set α where
    field
        isSemigroup : Semigroup _·_
        identity    : Identity  _·_ ε
    open Semigroup isSemigroup public
    open Identity identity public

Commutative : ∀ {α} {A : Set α} (_·_ : A → A → A) -> Set α
Commutative _·_ = ∀ x y → (x · y) ≡ (y · x)

record CommutativeMonoid {α} {A : Set α} (_·_ : A → A → A) (ε : A) : Set α where
    field
        isMonoid : Monoid      _·_ ε
        comm     : Commutative _·_
    open Monoid isMonoid public

LeftInverse : ∀ {α} {A : Set α} (_·_ : A → A → A) (ε : A) (_⁻¹ : A → A) -> Set α
LeftInverse _·_ ε _⁻¹ = ∀ a → ((a ⁻¹) · a) ≡ ε

RightInverse : ∀ {α} {A : Set α} (_·_ : A → A → A) (ε : A) (_⁻¹ : A → A) -> Set α
RightInverse _·_ ε _⁻¹ = ∀ a → (a · (a ⁻¹)) ≡ ε

record Group {α} {A : Set α} (_·_ : A → A → A) (ε : A) (_⁻¹ : A → A) : Set α where
    field
        isMonoid : Monoid _·_ ε
        inverse-l : LeftInverse _·_ ε _⁻¹
        inverse-r : RightInverse _·_ ε _⁻¹
    open Monoid isMonoid public

Involutive : ∀ {α} {A : Set α} (f : A → A) -> Set α
Involutive f = ∀ x → f (f x) ≡ x

[x⁻¹]⁻¹≡x
    : ∀ {α} {A : Set α}
    → (_·_ : A → A → A) (ε : A) (_⁻¹ : A → A) (g : Group _·_ ε _⁻¹)
    → Involutive _⁻¹
[x⁻¹]⁻¹≡x _·_ ε _⁻¹ g x =
    begin
        (x ⁻¹) ⁻¹
    ≡⟨ symm (Group.right-id g _) ⟩
        ((x ⁻¹) ⁻¹) · ε
    ≡⟨ cong (λ e → _ · e) (symm (Group.inverse-l g x)) ⟩
        ((x ⁻¹) ⁻¹) · ((x ⁻¹) · x)
    ≡⟨ symm (Group.assoc g _ _ _) ⟩
        (((x ⁻¹) ⁻¹) · (x ⁻¹)) · x
    ≡⟨ cong (λ e → e · _) (Group.inverse-l g _) ⟩
        ε · x
    ≡⟨ Group.left-id g x ⟩
        x
    qed

record AbelianGroup {α} {A : Set α} (_·_ : A → A → A) (ε : A) (_⁻¹ : A → A) : Set α where
    field
        isGroup : Group _·_ ε _⁻¹
        comm : Commutative _·_
    open Group isGroup public

abelianToCMonoid
    : ∀ {α} {A : Set α} {_·_} {ε : A} {_⁻¹}
    → AbelianGroup _·_ ε _⁻¹
    → CommutativeMonoid _·_ ε
abelianToCMonoid g = record
    { isMonoid = AbelianGroup.isMonoid g
    ; comm = AbelianGroup.comm g }
