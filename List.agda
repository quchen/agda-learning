module List where



open import Nat
open import Equality
open import Logic
open Equality.≡-Reasoning


infixr 6 _∷_
data List {α} (a : Set α) : Set α where
    [] : List a
    _∷_ : (x : a) → (xs : List a) → List a

foldr : ∀ {α β} {a : Set α} {b : Set β} → b → (a → b → b) → List a → b
foldr z f [] = z
foldr z f (x ∷ xs) = f x (foldr z f xs)

[_] : ∀ {α} {a : Set α} → a → List a
[ x ] = x ∷ []

_++_ : ∀ {α} {a : Set α} → List a → List a → List a
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : ∀ {α} {a : Set α} → List a → ℕ
length [] = 0
length (_ ∷ xs) = 1 + length xs

length[xs++ys]≡length[xs]+length[ys]
    : ∀ {α} {a : Set α} (xs ys : List a)
    → length (xs ++ ys) ≡ length xs + length ys
length[xs++ys]≡length[xs]+length[ys] [] ys = refl
length[xs++ys]≡length[xs]+length[ys] (x ∷ xs) ys = cong succ (length[xs++ys]≡length[xs]+length[ys] xs ys)

length[xs++ys]≡length[ys++xs]
    : ∀ {α} {a : Set α} (xs ys : List a)
    → length (xs ++ ys) ≡ length (ys ++ xs)
length[xs++ys]≡length[ys++xs] xs ys =
    begin
        length (xs ++ ys)
    ≡⟨ length[xs++ys]≡length[xs]+length[ys] xs ys ⟩
        length xs + length ys
    ≡⟨ comm-+ (length xs) (length ys) ⟩
        length ys + length xs
    ≡⟨ symm (length[xs++ys]≡length[xs]+length[ys] ys xs) ⟩
        length (ys ++ xs)
    qed

-- Computationally inefficient, but easy for theorem proving :-)
reverse : ∀ {α} {a : Set α} → List a → List a
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

module reverse-equivalence where

    -- The usual linear reverse implementation
    reverse' : ∀ {α} {a : Set α} → List a → List a
    reverse' = go []
      where
        go : ∀ {α} {a : Set α} → List a → List a → List a
        go xs [] = xs
        go xs (y ∷ ys) = go (y ∷ xs) ys

    reverse[xs]≡reverse'[xs]
        : ∀ {α} {a : Set α} (xs : List a)
        → reverse xs ≡ reverse' xs
    reverse[xs]≡reverse'[xs] [] = refl
    reverse[xs]≡reverse'[xs] (x ∷ xs) = {!   !}

length[reverse[xs]]≡length[xs]
    : ∀ {α} {a : Set α} (xs : List a)
    → length (reverse xs) ≡ length xs
length[reverse[xs]]≡length[xs] [] = refl
length[reverse[xs]]≡length[xs] (x ∷ xs) =
    begin
        length (reverse xs ++ (x ∷ []))
    ≡⟨ length[xs++ys]≡length[xs]+length[ys] (reverse xs) [ x ] ⟩
        length (reverse xs) + length [ x ]
    ≡⟨ refl ⟩
        length (reverse xs) + 1
    ≡⟨ comm-+ (length (reverse xs)) 1 ⟩
        1 + length (reverse xs)
    ≡⟨ cong succ (length[reverse[xs]]≡length[xs] xs) ⟩
        succ (length xs)
    qed

reverse[reverse[xs]]≡xs
    : ∀ {α} {a : Set α} (xs : List a)
    → reverse (reverse xs) ≡ xs
reverse[reverse[xs]]≡xs [] = refl
reverse[reverse[xs]]≡xs (x ∷ xs) = {!   !}

map
    : ∀ {α β} {a : Set α} {b : Set β}
    → (f : a → b) → (xs : List a) → List b
map _ [] = []
map f (x ∷ xs) = f x ∷ map f xs

length[map[f][xs]]≡length[xs]
    : ∀ {α β} {a : Set α} {b : Set β} (f : a → b) (xs : List a)
    → length (map f xs) ≡ length xs
length[map[f][xs]]≡length[xs] _ [] = refl
length[map[f][xs]]≡length[xs] f (x ∷ xs) = cong succ (length[map[f][xs]]≡length[xs] f xs)

take
    : ∀ {α} {a : Set α}
    → ℕ → List a → List a
take zero _ = []
take _ [] = []
take (succ n) (x ∷ xs) = x ∷ take n xs

drop'
    : ∀ {α} {a : Set α}
    → ℕ → List a → List a
drop' zero xs = xs
drop' _ [] = []
drop' (succ n) (x ∷ xs) = drop' n xs

splitAt
    : ∀ {a : Set}
    → ℕ → List a → List a ∧ List a
splitAt zero ys = ⟨ [] , ys ⟩
splitAt n [] = ⟨ [] , [] ⟩
splitAt (succ n) (x ∷ xs) with splitAt n xs
splitAt (succ n) (x ∷ _) | ⟨ ys , zs ⟩ = ⟨ x ∷ ys , zs ⟩

module splitAt-take-drop where

    splitAt-keeps-all-elements
        : ∀ {a : Set}
        → (n : ℕ) → (xs : List a)
        → length (proj₁ (splitAt n xs)) + length (proj₂ (splitAt n xs)) ≡ length xs
    splitAt-keeps-all-elements n xs = {!   !}

    splitAt[xs]≡⟨take[xs],drop[xs]⟩
        : ∀ {a : Set}
        → (n : ℕ) → (xs : List a)
        → splitAt n xs ≡ ⟨ take n xs , drop' n xs ⟩
    splitAt[xs]≡⟨take[xs],drop[xs]⟩ zero [] = refl
    splitAt[xs]≡⟨take[xs],drop[xs]⟩ zero (x ∷ xs) = refl
    splitAt[xs]≡⟨take[xs],drop[xs]⟩ (succ n) [] = refl
    splitAt[xs]≡⟨take[xs],drop[xs]⟩ (succ n) (x ∷ xs) = {!   !}

-- _!_ : ∀ {a} → (xs : List a) → (n : ℕ) → {p : length xs ≤ n} → a
-- [] ! n = {!   !}
-- (x ∷ _) ! zero = x
-- (_ ∷ xs) ! succ n = xs ! n

infixr 3 _⊆_
infixr 3 _⊈_
data _⊆_ {a : Set} : List a → List a → Set where
    stop : [] ⊆ []
    drop : ∀ {x xs ys} → xs ⊆ ys →     xs ⊆ x ∷ ys
    keep : ∀ {x xs ys} → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys

_⊈_ : ∀ {a} → List a → List a → Set
xs ⊈ ys = ¬ (xs ⊆ ys)

[]⊆xs : ∀ {a} {xs : List a} → [] ⊆ xs
[]⊆xs {xs = []} = stop
[]⊆xs {xs = x ∷ xs} = drop []⊆xs

drop←
    : ∀ {a} {x : a} {xs ys : List a}
    → (_∷_ x xs) ⊆ ys → xs ⊆ ys
drop← {xs = []} _ = []⊆xs
drop← {ys = _ ∷ _} (drop ξ∷x∷xs⊆ys) = drop (drop← ξ∷x∷xs⊆ys)
drop← {ys = _ ∷ _} (keep x∷xs⊆ys) = drop x∷xs⊆ys

-- Case -> autoderive
refl-⊆ : ∀ {a} {xs : List a} → xs ⊆ xs
refl-⊆ {xs = []} = stop
refl-⊆ {xs = x ∷ xs} = keep refl-⊆

trans-⊆
    : ∀ {a} {xs ys zs : List a}
    → xs ⊆ ys
    → ys ⊆ zs
    → xs ⊆ zs
trans-⊆ stop stop = stop
trans-⊆ stop (drop q) = drop q
trans-⊆ (drop p) (drop q) = drop (trans-⊆ p (drop← q))
trans-⊆ (drop p) (keep q) = drop (trans-⊆ p q)
trans-⊆ (keep p) (drop q) = drop (trans-⊆ (keep p) q)
trans-⊆ (keep p) (keep q) = keep (trans-⊆ p q)


module Sublist where
    infixr 6 _∷_
    data Sublist {A : Set} : List A → Set where
        [] : Sublist []
        _∷_ : ∀ x {xs} → Sublist xs → Sublist (x ∷ xs)
        skip : ∀ {x xs} → Sublist xs → Sublist (x ∷ xs)

    forget : ∀ {A : Set} {xs : List A} → Sublist xs → List A
    forget [] = []
    forget (x ∷ xs) = x ∷ forget xs
    forget (skip xs) = forget xs
        -- Interesting (caught) bug here if we add the x to the result in error.
        -- Type system at work!

    inject : {A : Set} → (xs : List A) → Sublist xs
    inject [] = []
    inject (x ∷ xs) = x ∷ inject xs

    forget∘inject≡id : {A : Set} {xs : List A} → forget (inject xs) ≡ xs
    forget∘inject≡id {xs = []} = refl
    forget∘inject≡id {xs = x ∷ xs} = cong (λ e → x ∷ e) forget∘inject≡id

    sublist-implies-⊆
        : ∀ {A : Set} {xs : List A}
        → (ys : Sublist xs)
        → forget ys ⊆ xs
    sublist-implies-⊆ [] = stop
    sublist-implies-⊆ (_ ∷ ys) = keep (sublist-implies-⊆ ys)
    sublist-implies-⊆ (skip ys) = drop (sublist-implies-⊆ ys)

    filter : ∀ {A : Set} → (p : A → Bool) → (xs : List A) → Sublist xs
    filter _ [] = []
    filter p (x ∷ xs) with p x
    filter p (x ∷ xs) | true = x ∷ filter p xs
    filter p (x ∷ xs) | false = skip (filter p xs)

    complement
        : {A : Set} {xs : List A}
        → Sublist xs
        → Sublist xs
    complement [] = []
    complement (x ∷ ys) = skip (complement ys)
    complement {xs = x ∷ _} (skip ys) = x ∷ complement ys

    complement²≡id
        : {A : Set} {xs : List A}
        → (ys : Sublist xs)
        → complement (complement ys) ≡ ys
    complement²≡id [] = refl
    complement²≡id (x ∷ ys) = cong (λ e → x ∷ e) (complement²≡id ys)
    complement²≡id {xs = x ∷ _} (skip ys) = cong skip (complement²≡id ys)

    sublists : {A : Set} → (xs : List A) → List (Sublist xs)
    sublists [] = []
    sublists (x ∷ xs) = {!   !}

module Element where

    infixr 5 _∈_
    data _∈_ {A : Set} : A → List A → Set where
        here : ∀ {e xs} → e ∈ e ∷ xs
        there : ∀ {e x xs} → e ∈ xs → e ∈ x ∷ xs

    open Sublist

    x∈xs⇒[x]⊆xs : ∀ {A} {x : A} xs → x ∈ xs → [ x ] ⊆ xs
    x∈xs⇒[x]⊆xs [] ()
    x∈xs⇒[x]⊆xs (x ∷ xs) here = keep []⊆xs
    x∈xs⇒[x]⊆xs (x ∷ xs) (there x∈xs) = drop (x∈xs⇒[x]⊆xs xs x∈xs)

    trans-∈ : ∀ {A} {x : A} {xs} {ys} → x ∈ xs → xs ⊆ ys → x ∈ ys
    trans-∈ {xs = []} {[]} () q
    trans-∈ {xs = []} {x₁ ∷ ys} () q
    trans-∈ {xs = _ ∷ xs} {[]} here ()
    trans-∈ {xs = x ∷ xs} {[]} (there p) ()
    trans-∈ {xs = _ ∷ xs} {x ∷ ys} here (drop q) = {!    !}
    trans-∈ {xs = _ ∷ xs} {_ ∷ ys} here (keep q) = here
    trans-∈ {xs = x₁ ∷ xs} {x ∷ ys} (there p) (drop q) = {!   !}
    trans-∈ {xs = x ∷ xs} {.x ∷ ys} (there p) (keep q) = there (trans-∈ p q)

notHead :
