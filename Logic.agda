module Logic where

open import Algebra
open import Equality

data ⊤ : Set where
    tt : ⊤

data ⊥ : Set where

exFalso : ∀ {α} {a : Set α} → ⊥ → a
exFalso ()

infix 5 ¬_
¬_ : Set → Set
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
data _∨_ (A B : Set) : Set where
    inl : (a : A) → A ∨ B
    inr : (b : B) → A ∨ B

data Bool : Set where
    true  : Bool
    false : Bool

bool : Bool → Set
bool true  = ⊤
bool false = ⊥

data Dec (P : Set) : Set where
    yes :   P → Dec P
    no  : ¬ P → Dec P

⌊_⌋ : {P : Set} → Dec P → Bool
⌊ yes x ⌋ = true
⌊ no  x ⌋ = false

∧-assoc-l : ∀ {P Q R} → P ∧ (Q ∧ R) → (P ∧ Q) ∧ R
∧-assoc-l ⟨ p , ⟨ q , r ⟩ ⟩ = ⟨ ⟨ p , q ⟩ , r ⟩

∧-assoc-r : ∀ {P Q R} → (P ∧ Q) ∧ R → P ∧ (Q ∧ R)
∧-assoc-r ⟨ ⟨ p , q ⟩ , r ⟩ = ⟨ p , ⟨ q , r ⟩ ⟩

∧-commute : ∀ {P Q} → P ∧ Q → Q ∧ P
∧-commute ⟨ p , q ⟩ = ⟨ q , p ⟩

∨-assoc-l : ∀ {P Q R} → P ∨ (Q ∨ R) → (P ∨ Q) ∨ R
∨-assoc-l (inl p)       = inl (inl p)
∨-assoc-l (inr (inl q)) = inl (inr q)
∨-assoc-l (inr (inr r)) = inr r

∨-assoc-r : ∀ {P Q R} → (P ∨ Q) ∨ R → P ∨ (Q ∨ R)
∨-assoc-r (inl (inl p)) = inl p
∨-assoc-r (inl (inr q)) = inr (inl q)
∨-assoc-r (inr r)       = inr (inr r)

∨-commute : ∀ {P Q} → P ∨ Q → Q ∨ P
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

record Σ (A : Set) (B : A → Set) : Set where
    constructor _,_
    field
        π₁ : A
        π₂ : B π₁

ind-Σ
    : ∀ {A : Set} {B : A → Set} {c : Set}
    → ((a : A) → B a → c) → Σ A B → c
ind-Σ f ( x , y ) = f x y

module AgdaExercises where
    -- Some logical exercises from
    -- https://www.cs.uoregon.edu/research/summerschool/summer15/notes/AgdaExercises.pdf

    LEM⇒DNE : ∀ {a} → (a ∨ ¬ a) → (¬ ¬ a → a)
    LEM⇒DNE (inl a) _ = a
    LEM⇒DNE (inr ¬a) ¬¬a = exFalso (¬¬a ¬a)

    -- Should not work: LEM⇐DNE

    -- Should work: (∀ a. DNE a) → (∀ a. LEM a)
    -- Holy shit, autoderive completely solves this
    ∀DNE⇒∀LEM : (∀ {a} → ¬ ¬ a → a) → (∀ {a} → (a ∨ ¬ a))
    ∀DNE⇒∀LEM = λ z {a} → z (λ z₁ → z₁ (inr (λ x → z₁ (inl x))))

    -- Should work: (∀ a. LEM a) → (∀ a. DNE a)
    -- Clever exercise! We can just commute all the ∀ to the very beginning, and
    -- then this becomes a special case of LEM⇒DNE. I don’t fully understand how
    -- this works, I think there’s something left to be learned about ∀ here.
    ∀LEM⇒∀DNE : (∀ {a} → (a ∨ ¬ a)) → (∀ {b} → ¬ ¬ b → b)
    ∀LEM⇒∀DNE x = LEM⇒DNE x

-- Woo I’m doing modules!
open AgdaExercises
