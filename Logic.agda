module Logic where

open import Algebra
open import Function
open import Agda.Primitive
open import Equality

module Top where

    data ⊤ : Set where
        tt : ⊤

open Top public

module Bottom where

    data ⊥ : Set where

    ind-⊥ : ∀ {α} {C : (x : ⊥) → Set α} → (x : ⊥) → C x
    ind-⊥ ()

open Bottom public

exFalso : ∀ {α} {A : Set α} → ⊥ → A
exFalso ()

infix 5 ¬_
¬_ : ∀ {α} → Set α → Set α
¬ a = a → ⊥

cancel-¬ : ∀ {α} {P : Set α} → ¬ ¬ ¬ P → ¬ P
cancel-¬ ¬¬¬p = λ p → ¬¬¬p (λ ¬p → ¬p p)

add-¬ : ∀ {α} {P : Set α} → P → ¬ (¬ P)
add-¬ p ¬p = ¬p p

infixr 2 _,_
record Σ {α β} (A : Set α) (B : A → Set β) : Set (α ⊔ β) where
    constructor _,_
    field
        π₁ : A
        π₂ : B π₁

ind-Σ
    : ∀ {α β γ} {A : Set α} {B : A → Set β} {C : Set γ}
    → ((a : A) → B a → C) → Σ A B → C
ind-Σ f ( x , y ) = f x y

infix 3 _∧_
_∧_ : ∀ {α β} → Set α → Set β → Set (α ⊔ β)
A ∧ B = Σ A (const B)

infix 2 _×_
_×_ : ∀ {α β} → Set α → Set β → Set (α ⊔ β)
_×_ = _∧_

infix 2 _∨_
data _∨_ {α β} (A : Set α) (B : Set β) : Set (α ⊔ β) where
    inl : (l : A) → A ∨ B
    inr : (r : B) → A ∨ B

data Dec {α} (P : Set α) : Set α where
    yes : ( p :   P) → Dec P
    no  : (¬p : ¬ P) → Dec P

module Decidable where

    module Unary where
        -- »LEM holds for this predicate«
        Decidable
            : ∀ {α β} {A : Set α}
            → (A → Set β)
            → Set (α ⊔ β)
        Decidable P = ∀ x → Dec (P x)

    module Binary where
        -- »LEM holds for this binary relation«
        Decidable
            : ∀ {α β γ} {A : Set α} {B : Set β}
            → (A → B → Set γ)
            → Set (α ⊔ β ⊔ γ)
        Decidable _~_ = ∀ x y → Dec (x ~ y)

∧-assoc-l : ∀ {α β γ} {P : Set α} {Q : Set β} {R : Set γ} → P ∧ (Q ∧ R) → (P ∧ Q) ∧ R
∧-assoc-l (p , (q , r)) = ((p , q) , r)

∧-assoc-r : ∀ {α β γ} {P : Set α} {Q : Set β} {R : Set γ} → (P ∧ Q) ∧ R → P ∧ (Q ∧ R)
∧-assoc-r ((p , q) , r) = (p , (q , r))

∧-commute : ∀ {α β} {P : Set α} {Q : Set β} → P ∧ Q → Q ∧ P
∧-commute (p , q) = (q , p)

∨-assoc-l : ∀ {α} {P Q R : Set α} → P ∨ (Q ∨ R) → (P ∨ Q) ∨ R
∨-assoc-l (inl p)       = inl (inl p)
∨-assoc-l (inr (inl q)) = inl (inr q)
∨-assoc-l (inr (inr r)) = inr r

∨-assoc-r : ∀ {α} {P Q R : Set α} → (P ∨ Q) ∨ R → P ∨ (Q ∨ R)
∨-assoc-r (inl (inl p)) = inl p
∨-assoc-r (inl (inr q)) = inr (inl q)
∨-assoc-r (inr r)       = inr (inr r)

∨-commute : ∀ {α} {P Q : Set α} → P ∨ Q → Q ∨ P
∨-commute (inl p) = inr p
∨-commute (inr q) = inl q

deMorgan₁ : ∀ {α β} {P : Set α} {Q : Set β} → ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)
deMorgan₁ ¬⟨p∨q⟩ = ((λ p → ¬⟨p∨q⟩ (inl p)) , (λ q → ¬⟨p∨q⟩ (inr q)))

deMorgan₂ : ∀ {α β} {P : Set α} {Q : Set β} → (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)
deMorgan₂ (¬p , _) (inl p) = ¬p p
deMorgan₂ (_ , ¬q) (inr q) = ¬q q

deMorgan₃ : ∀ {α β} {P : Set α} {Q : Set β} → (¬ P ∨ ¬ Q) → ¬ (P ∧ Q)
deMorgan₃ (inl ¬p) (p , _) = ¬p p
deMorgan₃ (inr ¬q) (_ , q) = ¬q q

distr-∨∧ : ∀ {α β γ} {P : Set α} {Q : Set β} {R : Set γ} → (P ∨ Q) ∧ R → (P ∧ R) ∨ (Q ∧ R)
distr-∨∧ (inl p , r) = inl (p , r)
distr-∨∧ (inr q , r) = inr (q , r)

distr-∧∨ : ∀ {α β γ} {P : Set α} {Q : Set β} {R : Set γ} → (P ∧ Q) ∨ R → (P ∨ R) ∧ (Q ∨ R)
distr-∧∨ (inl (p , q)) = (inl p , inl q)
distr-∧∨ (inr r) = (inr r , inr r)

rdistr-∧∨∧ : ∀ {α β γ} {P : Set α} {Q : Set β} {R : Set γ} → (P ∧ R) ∨ (Q ∧ R) → (P ∨ Q) ∧ R
rdistr-∧∨∧ (inl (p , r)) = (inl p , r)
rdistr-∧∨∧ (inr (q , r)) = (inr q , r)

rdistr-∨∧∨ : ∀ {α β γ} {P : Set α} {Q : Set β} {R : Set γ} → (P ∨ R) ∧ (Q ∨ R) → (P ∧ Q) ∨ R
rdistr-∨∧∨ (inl p , inl q) = inl (p , q)
rdistr-∨∧∨ (inl p , inr r) = inr r
rdistr-∨∧∨ (inr r , _) = inr r

-- Σ constructor, but auto-infer the witness type.
∃ : ∀ {α β} {A : Set α} → (A → Set β) → Set (α ⊔ β)
∃ = Σ _

module AgdaExercises where
    -- Some logical exercises from
    -- https://www.cs.uoregon.edu/research/summerschool/summer15/notes/AgdaExercises.pdf

    ∀⟨LEM⇒DNE⟩ : ∀ {α} {A : Set α} → (A ∨ ¬ A) → (¬ ¬ A → A)
    ∀⟨LEM⇒DNE⟩ (inl a) _ = a
    ∀⟨LEM⇒DNE⟩ (inr ¬a) ¬¬a = exFalso (¬¬a ¬a)

    -- Should not work: LEM⇐DNE

    -- Should work: (∀ a. DNE a) → (∀ a. LEM a)
    -- Holy shit, autoderive completely solves this
    ∀DNE⇒∀LEM : (∀ {α} {A : Set α} → ¬ ¬ A → A) → (∀ {β} {B : Set β} → (B ∨ ¬ B))
    ∀DNE⇒∀LEM = λ ¬¬a⇒a → ¬¬a⇒a (λ ¬⟨b∨¬b⟩ → ¬⟨b∨¬b⟩ (inr (λ b → ¬⟨b∨¬b⟩ (inl b))))

    -- Should work: (∀ a. LEM a) → (∀ a. DNE a)
    -- Clever exercise! We can just commute all the ∀ to the very beginning, and
    -- then this becomes a special case of LEM⇒DNE. I don’t fully understand how
    -- this works, I think there’s something left to be learned about ∀ here.
    ∀LEM⇒∀DNE : (∀ {α} {A : Set α} → (A ∨ ¬ A)) → (∀ {β} {B : Set β} → ¬ ¬ B → B)
    ∀LEM⇒∀DNE x = ∀⟨LEM⇒DNE⟩ x

    private
        ∀LEM⇒∀DNE-with-with : (∀ (A : Set) → (A ∨ ¬ A)) → (∀ {B : Set} → ¬ ¬ B → B)
        ∀LEM⇒∀DNE-with-with x {b} _ with x b
        ∀LEM⇒∀DNE-with-with _ _ | inl b = b
        ∀LEM⇒∀DNE-with-with _ ¬¬b | inr ¬b = exFalso (¬¬b ¬b)

-- Woo I’m doing modules!
open AgdaExercises

-- Exercise given as an aside in »how many is two«, a nice article about sets of
-- truth values.
-- http://math.andrej.com/2005/05/16/how-many-is-two/
andrejsTheorem : ∀ {α} {P : Set α} → ¬ (¬ P ∧ ¬ ¬ P)
andrejsTheorem (¬p , ¬¬p) = ¬¬p ¬p

-- Π type (dependent function), for when we want to make Agda as awkward to read
-- as HoTT ;-)
Π : (A : Set) → (B : A → Set) → Set
Π A B = (x : A) → B x

private
    -- Recover the function arrow from the dependent function type Π
    _⟶_ : Set → Set → Set
    A ⟶ B = Π A (λ _ → B)
