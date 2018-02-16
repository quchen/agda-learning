module List where



open import Nat
open import Function
open import Equality
open import Bool
open import Logic
open Equality.≡-Reasoning



infixr 6 _∷_
data List {α} (a : Set α) : Set α where
    [] : List a
    _∷_ : (x : a) → (xs : List a) → List a
{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

foldr : ∀ {α β} {a : Set α} {b : Set β} → b → (a → b → b) → List a → b
foldr z f [] = z
foldr z f (x ∷ xs) = f x (foldr z f xs)

[_] : ∀ {α} {a : Set α} → a → List a
[ x ] = x ∷ []

infixr 5 _++_
_++_ : ∀ {α} {a : Set α} → List a → List a → List a
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

NonEmpty : ∀ {α} {A : Set α} (xs : List A) → Set
NonEmpty [] = ⊥
NonEmpty (_ ∷ _) = ⊤

head : ∀ {α} {A : Set α} (xs : List A) → NonEmpty xs → A
head [] ()
head (x ∷ _) _ = x

module head-example where
    myList : List ℕ
    myList = 0  ∷ 1 ∷ 2 ∷ []

    myList-head : ℕ
    myList-head = head myList (record {})

tail : ∀ {α} {A : Set α} (xs : List A) → NonEmpty xs → List A
tail [] ()
tail (_ ∷ xs) _ = xs

private
    -- We cannot write the `head` function, proof:
    notHead : ¬ (∀ {A} → List A → A)
    notHead head = head []
    -- The [] is of type [⊥], and since we claim we can get the first element
    -- out of *any* list, we just take the first ⊥ out of that list.

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

-- Computationally inefficient, but easier for theorem proving :-)
reverse : ∀ {α} {a : Set α} → List a → List a
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

module reverse-equivalence where

    reverse-helper : ∀ {α} {a : Set α} → List a → List a → List a
    reverse-helper xs [] = xs
    reverse-helper xs (y ∷ ys) = reverse-helper (y ∷ xs) ys

    -- The usual linear reverse implementation
    reverse' : ∀ {α} {a : Set α} → List a → List a
    reverse' = reverse-helper []

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
splitAt zero ys = ([] , ys)
splitAt n [] = ([] , [])
splitAt (succ n) (x ∷ xs) with splitAt n xs
splitAt (succ n) (x ∷ _) | (ys , zs) = (x ∷ ys , zs)

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

drop-head
    : ∀ {a} {x : a} {xs ys : List a}
    → (_∷_ x xs) ⊆ ys → xs ⊆ ys
drop-head {xs = []} _ = []⊆xs
drop-head {ys = _ ∷ _} (drop ξ∷x∷xs⊆ys) = drop (drop-head ξ∷x∷xs⊆ys)
drop-head {ys = _ ∷ _} (keep x∷xs⊆ys) = drop x∷xs⊆ys

drop-tail
    : ∀ {a} {x : a} {xs ys : List a}
    → (_∷_ x xs) ⊆ ys → [ x ] ⊆ ys
drop-tail (drop xs) = drop (drop-tail xs)
drop-tail (keep _) = keep []⊆xs

-- Case -> autoderive
refl-⊆ : ∀ {a} {xs : List a} → xs ⊆ xs
refl-⊆ {xs = []} = stop
refl-⊆ {xs = _ ∷ _} = keep refl-⊆

trans-⊆
    : ∀ {a} {xs ys zs : List a}
    → xs ⊆ ys
    → ys ⊆ zs
    → xs ⊆ zs
trans-⊆ stop stop = stop
trans-⊆ stop (drop q) = drop q
trans-⊆ (drop p) (drop q) = drop (trans-⊆ p (drop-head q))
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

    head-subset : ∀ {A} {x : A} {xs ys} → x ∷ xs ⊆ ys → [ x ] ⊆ ys
    head-subset (drop xs) = drop (head-subset xs)
    head-subset (keep _) = keep []⊆xs

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
    … | true = x ∷ filter p xs
    … | false = skip (filter p xs)

    complement
        : {A : Set} {xs : List A}
        → Sublist xs
        → Sublist xs
    complement [] = []
    complement (x ∷ ys) = skip (complement ys)
    complement (skip {x = x} ys) = x ∷ complement ys

    complement²≡id
        : {A : Set} {xs : List A}
        → (ys : Sublist xs)
        → complement (complement ys) ≡ ys
    complement²≡id [] = refl
    complement²≡id (_ ∷ ys) rewrite complement²≡id ys = refl
    complement²≡id (skip ys) rewrite complement²≡id ys = refl

    sublists : {A : Set} → (xs : List A) → List (Sublist xs)
    sublists [] = []
    sublists (x ∷ xs) = map skip (sublists xs) ++ map (_∷_ x) (sublists xs)

module Element where

    infixr 5 _∈_
    data _∈_ {A : Set} : A → List A → Set where
        here : ∀ {e xs} → e ∈ e ∷ xs
        there : ∀ {e x xs} → e ∈ xs → e ∈ x ∷ xs

    open Sublist

    inject-∈→⊆ : ∀ {A} {x : A} {xs} → x ∈ xs → [ x ] ⊆ xs
    inject-∈→⊆ here = keep []⊆xs
    inject-∈→⊆ (there x∈xs) = drop (inject-∈→⊆ x∈xs)

    extract-⊆→∈ : ∀ {A} {x : A} {xs} → [ x ] ⊆ xs → x ∈ xs
    extract-⊆→∈ (drop [x]⊆xs) = there (extract-⊆→∈ [x]⊆xs)
    extract-⊆→∈ (keep _) = here

    trans-∈ : ∀ {A} {x : A} {xs} {ys} → x ∈ xs → xs ⊆ ys → x ∈ ys
    trans-∈ x∈xs xs⊆ys = extract-⊆→∈ (trans-⊆ (inject-∈→⊆ x∈xs) xs⊆ys)

-- I can’t get this to typecheck without the »as« parameter in the »f«. But
-- doesn’t this make the induction on lists more powerful than the usual
-- »foldr«, since it has the whole rest of the list available on recursion?
-- What’s this called again, a histomorphism or something?
ind-List
    : ∀ {α} {A : Set α}
    → (C : List A → Set α)
    → (z : C [])
    → (f : (a : A) → (as : List A) → C as → C (a ∷ as))
    → (xs : List A)
    → C xs
ind-List C z f [] = z
ind-List C z f (x ∷ xs) = f x xs (ind-List C z f xs)

rec-List : ∀ {α} {A : Set α} {C : Set α} → C → (A → C → C) → List A → C
rec-List z _ [] = z
rec-List z f (x ∷ xs) = f x (rec-List z f xs)

rec-List-ind : ∀ {α} {A : Set α} {C : Set α} → C → (A → C → C) → List A → C
rec-List-ind {C = C} z f xs = ind-List (const C) z (λ a as x → f a x) xs
