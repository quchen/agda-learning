module Function where



open import Equality



id : ∀ {α} {a : Set α} → a → a
id x = x

-- Dependent function composition
_∘_
    : ∀ {α β γ} {A : Set α} {B : A → Set β} {C : {x : A} → B x → Set γ}
    → (f : {x : A} (y : B x) → C y)
    → (g : (x : A) → B x)
    → (x : A)
    → C (g x)
f ∘ g = λ x → f (g x)

-- Ordinary function composition
_∘'_
    : ∀ {α β γ} {a : Set α} {b : Set β} {c : Set γ}
    → (f : b → c)
    → (g : a → b)
    → (a → c)
f ∘' g = f ∘ g

assoc-∘
    : ∀ {α β γ δ} {a : Set α} {b : Set β} {c : Set γ} {d : Set δ}
    → (f : c → d) (g : b → c) (h : a → b) (x : a)
    → ((f ∘ g) ∘ h) x ≡ (f ∘ (g ∘ h)) x
assoc-∘ _ _ _ _ = refl

f∘id≡f : ∀ {α β} {a : Set α} {b : Set β} {x : a} (f : a → b) → (f ∘ id) x ≡ f x
f∘id≡f _ = refl

id∘f≡f : ∀ {α β} {a : Set α} {b : Set β} {x : a} (f : a → b) → (id ∘ f) x ≡ f x
id∘f≡f _ = refl

const : ∀ {α β} {A : Set α} {B : Set β} → A → B → A
const a _ = a

the : ∀ {α} (A : Set α) → A → A
the _ x = x
