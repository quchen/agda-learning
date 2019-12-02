module Homotopy where

open import Agda.Primitive
open import Equality
open import Logic
open import Function

-- Homotopy
_~_ : ∀ {α} {A : Set α} {P : A → Set α} → (f : (x : A) → P x) → (g : (y : A) → P y) → Set α
f ~ g = ∀ x → f x ≡ g x

-- Left-invertible functions
linv : ∀ {α β} {A : Set α} {B : Set β} → (A → B) → Set (α ⊔ β)
linv f = ∃ (λ g → (g ∘ f) ~ id)

-- Right-invertible functions
rinv : ∀ {α β} {A : Set α} {B : Set β} → (A → B) → Set (α ⊔ β)
rinv f = ∃ (λ g → (f ∘ g) ~ id)

-- Type equivalence
_≃_ : ∀ {α β} → (A : Set α) → (B : Set β) → Set (α ⊔ β)
A ≃ B = Σ (A → B) (λ f → rinv f × linv f)

private

    open import Bool

    _∨'_ : ∀ {α} → (A : Set α) → (B : Set α) → Set α
    A ∨' B = ∃ (rec-Bool A B)

    ⟶ : ∀ {α} {A : Set α} {B : Set α} → A ∨ B → A ∨' B
    ⟶ (inl l) = (true , l)
    ⟶ (inr r) = (false , r)

    ⟵ : ∀ {α} {A : Set α} {B : Set α} → A ∨' B → A ∨ B
    ⟵ (true , l) = inl l
    ⟵ (false , r) = inr r

    ⟵∘⟶=id : ∀ {α} {A : Set α} {B : Set α} (x : A ∨ B) → (⟵ ∘ ⟶) x ≡ id x
    ⟵∘⟶=id (inl l) = refl
    ⟵∘⟶=id (inr r) = refl

    ⟶∘⟵=id : ∀ {α} {A : Set α} {B : Set α} (x : A ∨' B) → (⟶ ∘ ⟵) x ≡ id x
    ⟶∘⟵=id (true , x) = refl
    ⟶∘⟵=id (false , x) = refl

    theorem
        : ∀ {α} {A : Set α} {B : Set α}
        → (A ∨ B) ≃ (A ∨' B)
    theorem = (⟶ , ((⟵ , ⟶∘⟵=id) , (⟵ , ⟵∘⟶=id)))
