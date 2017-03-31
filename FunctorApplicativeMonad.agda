module FunctorApplicativeMonad where

open import Function
open import Agda.Primitive
open import Equality

record Functor {α} (F : Set α → Set α) : Set (lsuc α) where
    field
        fmap : ∀ {A B : Set α} → (A → B) → F A → F B
        fmap[id]≡id : ∀ {A : Set α} {x : F A} → fmap id x ≡ x

record Applicative {α} (F : Set α → Set α) : Set (lsuc α) where
    infixl 4 _⟨*⟩_
    field
        pure : ∀ {A : Set α} → A → F A
        _⟨*⟩_ : ∀ {A B : Set α} → F (A → B) → F A → F B

        -- Laws
        isFunctor : Functor F
        fmap-from-Applicative
            : {A B : Set α} {f : A → B} {x : F A}
            → pure f ⟨*⟩ x ≡ Functor.fmap isFunctor f x
        homomorphism
            : {A B : Set α} {f : A → B} {x : A}
            → pure f ⟨*⟩ pure x ≡ pure (f x)
        interchange
            : {A B : Set α} {u : F (A → B)} {y : A}
            → u ⟨*⟩ pure y ≡ pure (λ f → f y) ⟨*⟩ u
        composition
            : {A B C : Set α} {u : F (B → C)} {v : F (A → B)} {w : F A}
            → u ⟨*⟩ (v ⟨*⟩ w) ≡ pure _∘_ ⟨*⟩ u ⟨*⟩ v ⟨*⟩ w

    open Functor isFunctor public

    -- LAWS!

record Monad {α} (F : Set α → Set α) : Set (lsuc α) where
    field
        isApplicative : Applicative F
        join : ∀ {A : Set α} → F (F A) → F A
        -- fmap[join]∘join≡join∘join : {A : Set α} {mmx : F (F A)} → Functor.fmap isApplicative join (join mmx) ≡ join (join mmx)

    open Applicative isApplicative public

    -- fmap[id]≡id : ∀ {A : Set α} {x : F A} → fmap id x ≡ x
