module Equality where

open import Agda.Primitive

infix 1 _≡_
data _≡_ {α} {A : Set α} (x : A) : A → Set α where
    refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

-- a ≡ b, but with explicit type argument.
Id : ∀ {α} (A : Set α) (x y : A) → Set α
Id _ x y = x ≡ y

-- refl, but with explicit arguments.
refl' : ∀ {α} (A : Set α) (x : A) → x ≡ x
refl' _ _ = refl

-- Neatly auto-derivable: case, match on equalty proof, auto.
ind-≡
    : ∀ {α β} {A : Set α}
    → (C : (a₁ a₂ : A) → a₁ ≡ a₂ → Set β)
    → (c : (a : A) → C a a refl)
    → (x y : A)
    → (p : x ≡ y)
    → C x y p
ind-≡ C c x .x refl = c x

symm
    : ∀ {α} {A : Set α} {x y : A}
    → x ≡ y
    → y ≡ x
symm refl = refl

private

    symm-via-ind : ∀ {α} {A : Set α} {x y : A} → x ≡ y → y ≡ x
    symm-via-ind {x = x} {y = y} x≡y
      = ind-≡ (λ a₁ a₂ _ → a₂ ≡ a₁)
              (λ _ → refl)
              x
              y
              x≡y

    trans-via-ind : ∀ {α} {A : Set α} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    trans-via-ind {x = x} {y = y} {z = z} x≡y
      = ind-≡ (λ a₁ a₂ _ → a₂ ≡ z → a₁ ≡ z)
              (λ _ refl → refl)
              x
              y
              x≡y

    subst-via-ind : ∀ {α β} {A : Set α} → {x y : A} → (P : A → Set β) → x ≡ y → P x → P y
    subst-via-ind {x = x} {y = y} p x≡y
      = ind-≡ (λ a₁ a₂ _ → p a₁ → p a₂)
              (λ _ refl → refl)
              x
              y
              x≡y


trans
    : ∀ {α} {A : Set α} {x y z : A}
    → x ≡ y
    → y ≡ z
    → x ≡ z
trans refl refl = refl

-- Congruency allows us to »scope into« definitions. In order to prove
--
-- > a + (b + c) ≡ a + (c + b)
--
-- for example, we can use »λ e → a + e« to scope into the »b+c« part,
--
-- > proof = cong (λ e → a + e) {! !}
--
-- The hole now has type »b+c ≡ c+b«. We thus scoped into the sum and isolated
-- the location we’d like to apply commutativity to.
cong
    : ∀ {α β} {A : Set α} {B : Set β} {x y : A}
    → (f : A → B)
    → x ≡ y
    → f x ≡ f y
cong _ refl = refl

subst
    : ∀ {α β} {A : Set α}
    → {x y : A}
    → (P : A → Set β)
    → x ≡ y
    → P x
    → P y
subst _ refl x = x

private
    trans-via-subst : ∀ {α} {A : Set α} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    trans-via-subst {z = z} eq₁ eq₂ = subst (λ e → e ≡ z) (symm eq₁) eq₂

subst₂
    : ∀ {α β} {A : Set α} {B : Set β}
    → {a₁ a₂ : A} {b₁ b₂ : B}
    → (P : A → B → Set β)
    → a₁ ≡ a₂
    → b₁ ≡ b₂
    → P a₁ b₁
    → P a₂ b₂
subst₂ _ refl refl Pa₁a₂ = Pa₁a₂

subst₃
    : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ}
    → {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C}
    → (P : A → B → C → Set β)
    → a₁ ≡ a₂
    → b₁ ≡ b₂
    → c₁ ≡ c₂
    → P a₁ b₁ c₁
    → P a₂ b₂ c₂
subst₃ _ refl refl refl Pa₁a₂a₃ = Pa₁a₂a₃

-- Nice way to write chains of equality proofs, courtesy of the Agda standard lib
module ≡-Reasoning {α} {A : Set α} where
    infix 3 _qed
    infixr 2 _≡⟨⟩_ _≡⟨_⟩_
    infix 1 begin_

    begin_ : {x y : A} → x ≡ y → x ≡ y
    begin_ x≡y = x≡y

    _≡⟨⟩_ : (x {y} : A) → x ≡ y → x ≡ y
    x ≡⟨⟩ x≡y = x≡y

    _≡⟨_⟩_ : (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
    _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

    _qed : (x : A) → x ≡ x
    _ qed = refl

unify : ∀ {α} {a : Set α} → a → a → a
unify x _ = x

-- Simple inspection type, taken from
-- http://agda.readthedocs.io/en/latest/language/with-abstraction.html#id16
data Inspect {α} {A : Set α} (x : A) : Set α where
    _with≡_ : (y : A) → x ≡ y → Inspect x

inspect : ∀ {α} {A : Set α} (x : A) → Inspect x
inspect x = x with≡ refl
