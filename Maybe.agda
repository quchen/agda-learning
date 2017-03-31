module Maybe where

open import Agda.Primitive
open import Equality
open import Function
open import FunctorApplicativeMonad

data Maybe {α} (A : Set α) : Set α where
    nothing : Maybe A
    just : A → Maybe A

fmap : ∀ {α} {A B : Set α} → (A → B) → Maybe A → Maybe B
fmap f nothing = nothing
fmap f (just x) = just (f x)

fmap[id]≡id : ∀ {α} {A : Set α} {x : Maybe A} → fmap id x ≡ x
fmap[id]≡id {x = nothing} = refl
fmap[id]≡id {x = just _} = refl

Maybe-Functor : ∀ {α} → Functor {α} Maybe
Maybe-Functor = record
    { fmap = fmap
    ; fmap[id]≡id = fmap[id]≡id }

pure : ∀ {α} {A : Set α} → A → Maybe A
pure = just

_⟨*⟩_ : ∀ {α} {A B : Set α} → Maybe (A → B) → Maybe A → Maybe B
just f ⟨*⟩ just x = just (f x)
_ ⟨*⟩ _ = nothing

fmap-from-Applicative
    : ∀ {α} {A B : Set α} {f : A → B} {x : Maybe A}
    → pure f ⟨*⟩ x ≡ fmap f x
fmap-from-Applicative {x = nothing} = refl
fmap-from-Applicative {x = just _} = refl

homomorphism
    : ∀ {α} {A B : Set α} {f : A → B} {x : A}
    → pure f ⟨*⟩ pure x ≡ pure (f x)
homomorphism = refl

Maybe-Applicative : ∀ {α} → Applicative {α} Maybe
Maybe-Applicative = record
    { isFunctor = Maybe-Functor
    ; pure = pure
    ; _⟨*⟩_ = _⟨*⟩_
    ; fmap-from-Applicative = fmap-from-Applicative
    ; homomorphism = homomorphism
    }
