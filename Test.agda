open import Agda.Primitive
open import Logic
open import Nat

p1 : ∀ n → ∃ (λ u → n < u)
p1 n = (succ n , refl-≤)

p2 : ∀ {α} n → ((y : Set α) → (∀ u → (n < u) → y) → y)
p2 zero = λ y x → x 1 (s≤s z≤n)
p2 (succ n) = λ y x → {!   !}

-- ∃x. T x  <==>  y => (x => T x => y) => y

==> : ∀ {α β} {T : Set α → Set β}
    → Σ (Set α) (λ x → T x)
    → (∀ {δ} {y : Set δ} → ((x : Set α) → T x → y) → y)
==> (x , Tx) f = f x Tx

<== : ∀ {α} (T : Set α → Set (lsuc α))
    → (∀ {y} → ((x : Set α) → T x → y) → y)
    → Σ (Set α) (λ x → T x)
Σ.π₁ (<== T f) = f (λ x _ → x)
Σ.π₂ (<== T f) = f {!   !}

id : {T : Set} → T → T
id x = x
