module Logic where

open import Algebra
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

exFalso : ∀ {α} {a : Set α} → ⊥ → a
exFalso ()

infix 5 ¬_
¬_ : ∀ {α} → Set α → Set α
¬ a = a → ⊥

cancel-¬ : {P : Set} → ¬ ¬ ¬ P → ¬ P
cancel-¬ ¬¬¬p = λ p → ¬¬¬p (λ ¬p → ¬p p)

add-¬ : {P : Set} → P → ¬ (¬ P)
add-¬ p ¬p = ¬p p

infix 3 _∧_
data _∧_ (A B : Set) : Set where
    ⟨_,_⟩ : (a : A) → (b : B) → (A ∧ B)

proj₁ : ∀ {P Q} → P ∧ Q → P
proj₁ ⟨ p , q ⟩ = p

proj₂ : ∀ {P Q} → P ∧ Q → Q
proj₂ ⟨ a , b ⟩ = b

infix 2 _∨_
data _∨_ {α} (A B : Set α) : Set α where
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

∧-assoc-l : ∀ {P Q R} → P ∧ (Q ∧ R) → (P ∧ Q) ∧ R
∧-assoc-l ⟨ p , ⟨ q , r ⟩ ⟩ = ⟨ ⟨ p , q ⟩ , r ⟩

∧-assoc-r : ∀ {P Q R} → (P ∧ Q) ∧ R → P ∧ (Q ∧ R)
∧-assoc-r ⟨ ⟨ p , q ⟩ , r ⟩ = ⟨ p , ⟨ q , r ⟩ ⟩

∧-commute : ∀ {P Q} → P ∧ Q → Q ∧ P
∧-commute ⟨ p , q ⟩ = ⟨ q , p ⟩

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

deMorgan₁ : ∀ {P Q} → ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)
deMorgan₁ ¬⟨p∨q⟩ = ⟨ (λ p → ¬⟨p∨q⟩ (inl p)) , (λ q → ¬⟨p∨q⟩ (inr q)) ⟩

deMorgan₂ : ∀ {P Q} → (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)
deMorgan₂ ⟨ ¬p , _ ⟩ (inl p) = ¬p p
deMorgan₂ ⟨ _ , ¬q ⟩ (inr q) = ¬q q

deMorgan₃ : ∀ {P Q} → (¬ P ∨ ¬ Q) → ¬ (P ∧ Q)
deMorgan₃ (inl ¬p) ⟨ p , _ ⟩ = ¬p p
deMorgan₃ (inr ¬q) ⟨ _ , q ⟩ = ¬q q

distr-∨∧ : ∀ {P Q R} → (P ∨ Q) ∧ R → (P ∧ R) ∨ (Q ∧ R)
distr-∨∧ ⟨ inl p , r ⟩ = inl ⟨ p , r ⟩
distr-∨∧ ⟨ inr q , r ⟩ = inr ⟨ q , r ⟩

distr-∧∨ : ∀ {P Q R} → (P ∧ Q) ∨ R → (P ∨ R) ∧ (Q ∨ R)
distr-∧∨ (inl ⟨ p , q ⟩) = ⟨ inl p , inl q ⟩
distr-∧∨ (inr R) = ⟨ inr R , inr R ⟩

rdistr-∧∨∧ : ∀ {P Q R} → (P ∧ R) ∨ (Q ∧ R) → (P ∨ Q) ∧ R
rdistr-∧∨∧ (inl ⟨ p , r ⟩) = ⟨ inl p , r ⟩
rdistr-∧∨∧ (inr ⟨ q , r ⟩) = ⟨ inr q , r ⟩

rdistr-∨∧∨ : ∀ {P Q R} → (P ∨ R) ∧ (Q ∨ R) → (P ∧ Q) ∨ R
rdistr-∨∧∨ ⟨ inl p , inl q ⟩ = inl ⟨ p , q ⟩
rdistr-∨∧∨ ⟨ inl p , inr r ⟩ = inr r
rdistr-∨∧∨ ⟨ inr r , _ ⟩ = inr r

infixr 2 _,_
record Σ {α β} (A : Set α) (B : A → Set β) : Set (α ⊔ β) where
    constructor _,_
    field
        π₁ : A
        π₂ : B π₁

ind-Σ
    : ∀ {A : Set} {B : A → Set} {c : Set}
    → ((a : A) → B a → c) → Σ A B → c
ind-Σ f ( x , y ) = f x y

-- Σ constructor, but auto-infer the witness type.
∃ : {A : Set} → (A → Set) → Set
∃ = Σ _

module AgdaExercises where
    -- Some logical exercises from
    -- https://www.cs.uoregon.edu/research/summerschool/summer15/notes/AgdaExercises.pdf

    LEM⇒DNE : ∀ {α} {a : Set α} → (a ∨ ¬ a) → (¬ ¬ a → a)
    LEM⇒DNE (inl a) _ = a
    LEM⇒DNE (inr ¬a) ¬¬a = exFalso (¬¬a ¬a)

    -- Should not work: LEM⇐DNE

    -- Should work: (∀ a. DNE a) → (∀ a. LEM a)
    -- Holy shit, autoderive completely solves this
    ∀DNE⇒∀LEM : (∀ {α} {a : Set α} → ¬ ¬ a → a) → (∀ {α} {a : Set α} → (a ∨ ¬ a))
    ∀DNE⇒∀LEM = λ z {a} → z (λ z₁ → z₁ (inr (λ x → z₁ (inl x))))

    -- Should work: (∀ a. LEM a) → (∀ a. DNE a)
    -- Clever exercise! We can just commute all the ∀ to the very beginning, and
    -- then this becomes a special case of LEM⇒DNE. I don’t fully understand how
    -- this works, I think there’s something left to be learned about ∀ here.
    ∀LEM⇒∀DNE : (∀ {α} {a : Set α} → (a ∨ ¬ a)) → (∀ {β} {b : Set β} → ¬ ¬ b → b)
    ∀LEM⇒∀DNE x = LEM⇒DNE x

-- Woo I’m doing modules!
open AgdaExercises

-- Exercise given as an aside in »how many is two«, a nice article about sets of
-- truth values.
-- http://math.andrej.com/2005/05/16/how-many-is-two/
andrejsTheorem : ∀ {P} → ¬ (¬ P ∧ ¬ ¬ P)
andrejsTheorem ⟨ ¬p , ¬¬p ⟩ = ¬¬p ¬p
