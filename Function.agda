module Function where



open import Equality



id : ∀ {α} {a : Set α} → a → a
id x = x

_∘_ : {a b c : Set} → (b → c) → (a → b) → (a → c)
f ∘ g = λ x → f (g x)

assoc-∘
    : ∀ {a b c d}
    → (f : c → d) (g : b → c) (h : a → b) (x : a)
    → ((f ∘ g) ∘ h) x ≡ (f ∘ (g ∘ h)) x
assoc-∘ _ _ _ _ = refl

f∘id≡f : ∀ {a b} (f : a → b) (x : a) → (f ∘ id) x ≡ f x
f∘id≡f _ _ = refl

id∘f≡f : ∀ {a b} (f : a → b) (x : a) → (id ∘ f) x ≡ f x
id∘f≡f _ _ = refl

const : ∀ {α β} {A : Set α} {B : Set β} → A → B → A
const a _ = a
