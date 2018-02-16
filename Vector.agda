module Vector where

open import Agda.Primitive
open import Equality
open import Algebra
open import Bool
open import Nat
open import Logic
import List as 𝕃
open import Fin
open import Function
open Equality.≡-Reasoning

infixr 6 _∷_
data Vec {α} (A : Set α) : ℕ → Set α where
    [] : Vec A 0
    _∷_ : ∀ {n} → (x : A) → (xs : Vec A n) → Vec A (succ n)

vec0≡[] : ∀ {α} {A : Set α} {xs : Vec A 0} → xs ≡ []
vec0≡[] {xs = []} = refl

-- Auto-derive!
head : ∀ {α n} {A : Set α} → Vec A (succ n) → A
head (x ∷ _) = x

-- Auto-derive!
tail : ∀ {α n} {a : Set α} → Vec a (succ n) → Vec a n
tail (_ ∷ xs) = xs

-- Auto-derive!
[_] : ∀ {α} {a : Set α} → a → Vec a 1
[ x ] = x ∷ []

-- Auto-derive!
_++_ : ∀ {α m n} {a : Set α} → Vec a m → Vec a n → Vec a (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- Nicely auto-derivable :-)
take
    : ∀ {α} {a : ℕ} {A : Set α}
    (b : ℕ) → Vec A a → Vec A (a ⊓ b)
take zero (_ ∷ _) = []
take zero [] = []
take _ [] = []
take (succ b) (x ∷ xs) = x ∷ take b xs

-- Nicely showcases subst.
-- I wonder whether this type uniquely specifies its value.
drop
    : ∀ {α} {a : ℕ} {A : Set α}
    (b : ℕ) → Vec A a → Vec A (a ∸ b)
drop _ [] = []
drop {a = a} {A = A} zero xs = subst (Vec A) (symm (x∸0≡x a)) xs -- ugh
drop (succ b) (x ∷ xs) = drop b xs

splitAt
    : ∀ {α} {a : ℕ} {A : Set α}
    → (b : ℕ) → Vec A a → Vec A (a ⊓ b) ∧ Vec A (a ∸ b)
splitAt zero [] = ([] , [])
splitAt zero (x ∷ xs) = ([] , x ∷ xs)
splitAt _ [] = ([] , [])
splitAt (succ b) (x ∷ xs) with splitAt b xs
splitAt (succ b) (x ∷ xs) | (as , bs) = (x ∷ as , bs)

module take-drop-splitAt where

    split=⟨take,drop⟩
        : ∀ {α} {a : ℕ} {A : Set α}
        → (b : ℕ) → (xs : Vec A a)
        → splitAt b xs ≡ (take b xs , drop b xs)
    split=⟨take,drop⟩ zero [] = refl
    split=⟨take,drop⟩ zero (x ∷ xs) = refl
    split=⟨take,drop⟩ (succ b) [] = refl
    split=⟨take,drop⟩ (succ b) (x ∷ xs) rewrite split=⟨take,drop⟩ b xs = refl

foldr : ∀ {α n} {a b : Set α} → (a → b → b) → b → Vec a n → b
foldr f z [] = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

concat : ∀ {α m n} {a : Set α} → Vec (Vec a m) n → Vec a (n * m)
concat [] = []
concat (xs ∷ xss) = xs ++ concat xss

reverse : ∀ {n} {a : Set} → Vec a n → Vec a n
reverse = reverse' []
  where
    reverse' : ∀ {m n} {a : Set} → Vec a m → Vec a n → Vec a (m + n)
    reverse' {m = m} {a = a} xs []
      = subst (λ e → Vec a e)
              (symm (x+0≡x m))
              xs
    reverse' {m = m} {n = succ n} {a = a} xs (y ∷ ys)
      = subst (λ e → Vec a e)
              (symm (x+[1+y]≡[1+x]+y m n))
              (reverse' (y ∷ xs) ys)

index : ∀ {n} {a : Set} → Fin n → Vec a n → a
index zero (x ∷ _) = x
index (succ n) (_ ∷ xs) = index n xs

replicate : ∀ {α n} {a : Set α} → a → Vec a n
replicate {n = zero} x = []
replicate {n = succ n} x = x ∷ replicate {n = n} x

module replicate-properties where
    replicate0≡[] : ∀ {α} {A : Set α} {x : A} → replicate {n = 0} x ≡ []
    replicate0≡[] = refl

-- Case split -> auto :-)
pointwiseApply : ∀ {n} {a b : Set} → Vec (a → b) n → Vec a n → Vec b n
pointwiseApply [] [] = []
pointwiseApply (f ∷ fs) (x ∷ xs) = f x ∷ pointwiseApply fs xs

-- Case -> Autoderive :-)
map : ∀ {α β n} {a : Set α} {b : Set β}
    → (a → b) → Vec a n → Vec b n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

-- Case split -> auto :-)
zip : ∀ {n} {a b : Set} → Vec a n → Vec b n → Vec (a ∧ b) n
zip [] [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys

-- Case split -> auto :-)
zipWith : ∀ {α n} {a b c : Set α} → (a → b → c) → Vec a n → Vec b n → Vec c n
zipWith f [] [] = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

module zipWith-properties where
    zipWith[]⁇≡[] : ∀ {α} {a b c : Set α} {f : a → b → c} {xs : Vec a 0} {ys : Vec b 0} → zipWith f [] ys ≡ []
    zipWith[]⁇≡[] {xs = []} {[]} = refl

    zipWith⁇[]≡[] : ∀ {α} {a b c : Set α} {f : a → b → c} {xs : Vec a 0} {ys : Vec b 0} → zipWith f xs [] ≡ []
    zipWith⁇[]≡[] {xs = []} {[]} = refl

tabulate : ∀ {n} {a : Set} → (Fin n → a) → Vec a n
tabulate {zero} f = []
tabulate {succ n} f = f zero ∷ tabulate (f ∘ succ)

module tabulate-test where
    square : ∀ {n} → Fin n → ℕ
    square = (λ n → n * n) ∘ toℕ

    test₁ : tabulate square ≡ 0 ∷ 1 ∷ 4 ∷ 9 ∷ 16 ∷ 25 ∷ 36 ∷ []
    test₁ = refl

transpose : ∀ {α m n} {a : Set α} → Vec (Vec a m) n → Vec (Vec a n) m
transpose [] = replicate []
transpose (xs ∷ xss) = zipWith _∷_ xs (transpose xss)

module matrix-test where
    testMatrix : Vec (Vec ℕ 3) 4
    testMatrix = ((11 ∷ 12 ∷ 13 ∷ [])
                ∷ (21 ∷ 22 ∷ 23 ∷ [])
                ∷ (31 ∷ 32 ∷ 33 ∷ [])
                ∷ (41 ∷ 42 ∷ 43 ∷ []) ∷ [])

    testTranspose : transpose testMatrix
        ≡ (11 ∷ 21 ∷ 31 ∷ 41 ∷ [])
        ∷ (12 ∷ 22 ∷ 32 ∷ 42 ∷ [])
        ∷ (13 ∷ 23 ∷ 33 ∷ 43 ∷ []) ∷ []
    testTranspose = refl

-- Auto-derivable :-)
index-is-inverse-of-tabulate
    : ∀ {n} {a : Set}
    → (f : Fin n → a) (i : Fin n) → index i (tabulate f) ≡ f i
index-is-inverse-of-tabulate f zero = refl
index-is-inverse-of-tabulate f (succ i) = index-is-inverse-of-tabulate (f ∘ succ) i

tabulate-is-inverse-of-index
    : ∀ {n} {a : Set}
    → (xs : Vec a n)
    → tabulate (λ k → index k xs) ≡ xs
tabulate-is-inverse-of-index [] = refl
tabulate-is-inverse-of-index (x ∷ xs) = cong (λ e → x ∷ e) (tabulate-is-inverse-of-index xs)

-- The pairs are autoderivable when the first component is known
filter : ∀ {α n} {A : Set α} → (A → Bool) → Vec A n → Σ ℕ (Vec A)
filter _ [] = zero , []
filter p (x ∷ xs) with p x | filter p xs
… | true  | (n , vs) = (succ n , x ∷ vs)
… | false | (n , vs) = (n , vs)

fromList : ∀ {α} {A : Set α} → 𝕃.List A → Σ ℕ (Vec A)
fromList 𝕃.[] = zero , []
fromList (x 𝕃.∷ xs) with fromList xs
fromList (x 𝕃.∷ xs) | n , vs = succ n , x ∷ vs

toList : ∀ {α n} {A : Set α} → Vec A n → 𝕃.List A
toList = foldr 𝕃._∷_ 𝕃.[]

module Sort where
    -- module first-attempt where
    --     Sorted' : ∀ {n} → Vec ℕ n → Set
    --     Sorted' [] = ⊤
    --     Sorted' (x ∷ []) = ⊤
    --     Sorted' (x₁ ∷ x₂ ∷ xs) with ⌊ x₁ ≤? x₂ ⌋
    --     … | true = Sorted' (x₂ ∷ xs)
    --     … | false = ⊥
    --
    --     insertSorted : ∀ {n} → ℕ → Vec ℕ n → Vec ℕ (succ n)
    --     insertSorted n [] = [ n ]
    --     insertSorted n (x ∷ xs) with ⌊ n ≤? x ⌋
    --     … | true = n ∷ x ∷ xs
    --     … | false = x ∷ insertSorted n xs
    --
    --     module insertSorted-preserves-sorted where
    --         test : ∀ {n} (x : ℕ) → (xs : Vec ℕ n) → Sorted' xs → Sorted' (insertSorted x xs)
    --         test _ [] _ = tt
    --         test x (y ∷ ys) x₂ with ⌊ x ≤? y ⌋
    --         test x (y ∷ ys) x₂ | true = {!   !}
    --         test x (y ∷ ys) x₂ | false = {!   !}
    --
    --     sort : ∀ {n} → Vec ℕ n → Vec ℕ n
    --     sort [] = []
    --     sort (x ∷ xs) = insertSorted x (sort xs)
    --
    -- module second-attempt where
    --
    --     data Sorted : ∀ {n} → Vec ℕ n → Set where
    --         [≤] : Sorted []
    --         [≤_] : (x : ℕ) → Sorted [ x ]
    --         _∷≤_
    --             : ∀ {k : ℕ} x₁ x₂ {xs : Vec ℕ k}
    --             → (p : x₁ ≤ x₂)
    --             → (ys : Sorted (_∷_ x₂ xs))
    --             → Sorted (_∷_ x₁ (_∷_ x₂ xs))
    --
    --     insertSorted : ∀ {n} → (x : ℕ) → Vec ℕ n → Vec ℕ (succ n)
    --     insertSorted x [] = [ x ]
    --     insertSorted x (y ∷ ys) with x ≤? y
    --     ... | yes _ = x ∷ y ∷ ys
    --     ... | no _ = y ∷ insertSorted x ys
    --
    --     insertSorted' : ∀ {n} {xs : Vec ℕ n} → (x : ℕ) → Sorted xs → Sorted (insertSorted x xs)
    --     insertSorted' zero [≤] = [≤ zero ]
    --     insertSorted' zero [≤ x ] = {!   !}
    --     insertSorted' zero ((x₁ ∷≤ x₂) p x₃) = {!   !}
    --     insertSorted' (succ x) [≤] = [≤ succ x ]
    --     insertSorted' (succ x₁) [≤ x ] = {!   !}
    --     insertSorted' (succ x) ((x₁ ∷≤ x₂) p x₃) = {!   !}
    --
    --     sort : ∀ {n} → (xs : Vec ℕ n) → Sorted xs
    --     sort [] = [≤]
    --     sort (x ∷ xs) with insertSorted x (sort xs)
    --     ... | foo = ?

    -- module third-attempt where
    --
    --     data Sorted : ∀ {n} → Vec ℕ n → Set where
    --         [≤] : Sorted []
    --         [≤_] : (x : ℕ) → Sorted [ x ]
    --         _≤_⟨_⟩∷_
    --             : ∀ {k} x₁ x₂ {xs : Vec ℕ k}
    --             → (p : x₁ ≤ x₂)
    --             → (ys : Sorted (_∷_ x₂ xs))
    --             → Sorted (_∷_ x₁ (_∷_ x₂ xs))
    --
    --     uncons
    --         : ∀ {k x₁ x₂} {x₁≤x₂ : x₁ ≤ x₂} {xs : Vec ℕ k}
    --         → Sorted (x₁ ∷ x₂ ∷ xs)
    --         → ℕ × ((x₁ ≤ x₂) × Sorted (x₂ ∷ xs))
    --     uncons (x ≤ _ ⟨ p ⟩∷ xs) = (x , p , xs)
    --
    --     Vecℕₛ : (n : ℕ) → Set
    --     Vecℕₛ n = Σ (Vec ℕ n) Sorted
    --
    --     merge : ∀ {nxs nys} → (xsₛ : Vecℕₛ nxs) → (ysₛ : Vecℕₛ nys) → Vecℕₛ (nxs + nys)
    --
    --     -- Empty list
    --     merge ([] , _) ysₛ = ysₛ
    --     merge xsₛ ([] , _) = subst Vecℕₛ (comm-+ 0 _) xsₛ
    --
    --     -- Merge of two singletons
    --     merge (x ∷ .[] , [≤ .x ]) (y ∷ .[] , [≤ .y ]) with x ≤? y
    --     … | yes x≤y = (x ∷ y ∷ [] , (x ≤ y ⟨ x≤y ⟩∷ [≤ y ]))
    --     … | no x≰y = (y ∷ x ∷ [] , y ≤ x ⟨ ¬⟨x≤y⟩⇒x≤y x≰y ⟩∷ [≤ x ])
    --
    --     -- Merge of a singleton with a list
    --     merge (x ∷ .[] , [≤ .x ]) (y₁ ∷ .(y₂ ∷ []) , (.y₁ ≤ y₂ ⟨ p ⟩∷ [≤ .y₂ ])) with x ≤? y₁
    --     … | yes x≤y₁ = (x ∷ y₁ ∷ y₂ ∷ [] , (x ≤ y₁ ⟨ x≤y₁ ⟩∷ (y₁ ≤ y₂ ⟨ p ⟩∷ [≤ y₂ ])))
    --     … | no x≰y₁ with {!   !}
    --     …     | foo = {!   !}
    --     merge (x ∷ .[] , [≤ .x ]) (y₁ ∷ _ , (.y₁ ≤ y₂ ⟨ p ⟩∷ (.y₂ ≤ x₂ ⟨ p₁ ⟩∷ sy))) = {!   !}
    --     -- … | yes x≤y₁ = (x ∷ y₁ ∷ y₂ ∷ ys , (x ≤ y₁ ⟨ x≤y₁ ⟩∷ (y₁ ≤ y₂ ⟨ p ⟩∷ sy)))
    --     -- … | no x≰y₁ with uncons sy
    --     -- …     | foo = ?
    --
    --     merge (x₁ ∷ _ , (.x₁ ≤ x₂ ⟨ p ⟩∷ sx)) (y ∷ .[] , [≤ .y ]) = {!   !}
    --     merge (x₁ ∷ _ , (.x₁ ≤ x₂ ⟨ x₁≤x₂ ⟩∷ sx)) (y₁ ∷ _ , (.y₁ ≤ y₂ ⟨ y₁≤y₂ ⟩∷ sy)) = {!   !}
    --     -- merge (x ∷ xs , sx) (y ∷ ys , sy) = {! sx sy  !}

    -- module fourth-attempt where
    --
    --     data Sorted : ∀ {n} → Vec ℕ n → Set where
    --         [≤] : Sorted []
    --         [≤_] : ∀ x → Sorted [ x ]
    --         _≤_⟨_⟩∷_
    --             : ∀ {k} x₁ x₂ {xs : Vec _ k}
    --             → (p : x₁ ≤ x₂)
    --             → (ys : Sorted (x₂ ∷ xs))
    --             → Sorted (x₁ ∷ x₂ ∷ xs)
    --
    --     insert : ∀ {n} {xs : Vec ℕ n} {ys : Vec ℕ (succ n)} x (ys≡x∷xs : ys ≡ x ∷ xs) → Sorted xs → Sorted ys
    --     insert x refl [≤] = [≤ x ]
    --     insert x refl [≤ y ] with x ≤? y
    --     insert x refl [≤ y ] | yes x≤y = x ≤ y ⟨ x≤y ⟩∷ [≤ y ]
    --     insert x refl [≤ y ] | no x≰y = {!   !} ≤ {!   !} ⟨ {!   !} ⟩∷ {!   !}
    --     insert x refl (y₁ ≤ y₂ ⟨ y₁≤y₂ ⟩∷ ys) with x ≤? y₁
    --     insert x refl (y₁ ≤ y₂ ⟨ y₁≤y₂ ⟩∷ ys) | yes x≤y₁ = x ≤ y₁ ⟨ x≤y₁ ⟩∷ (y₁ ≤ y₂ ⟨ y₁≤y₂ ⟩∷ ys)
    --     insert x refl (y₁ ≤ y₂ ⟨ y₁≤y₂ ⟩∷ ys) | no x≰y₁ with insert x refl ys
    --     ...                                         | foo = {! foo  !}
