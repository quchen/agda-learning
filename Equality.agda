module Equality where

open import Agda.Primitive

infix 1 _≡_
data _≡_ {α : Level} {A : Set α} (x : A) : A → Set where
    refl : x ≡ x

symm-≡
    : ∀ {α} {A : Set α} {x y : A}
    → x ≡ y
    → y ≡ x
symm-≡ refl = refl

trans-≡
    : ∀ {α} {A : Set α} {x y z : A}
    → x ≡ y
    → y ≡ z
    → x ≡ z
trans-≡ refl refl = refl

cong-≡
    : ∀ {α β} {A : Set α} {B : Set β} {x y : A}
    → (f : A → B)
    → x ≡ y
    → f x ≡ f y
cong-≡ _ refl = refl

subst-≡
    : ∀ {α β} {A : Set α} {P : A → Set β} {x y : A}
    → x ≡ y
    → P x
    → P y
subst-≡ refl Px = Px
