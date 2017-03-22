module Sign where



open import Algebra
open import Equality



data Sign : Set where
    + : Sign
    - : Sign

_*_ : Sign → Sign → Sign
+ * + = +
+ * - = -
- * + = -
- * - = +

+*x≡x : LeftIdentity _*_ +
+*x≡x + = refl
+*x≡x - = refl

x*+≡x : RightIdentity _*_ +
x*+≡x + = refl
x*+≡x - = refl

assoc-* : Associative _*_
assoc-* + + + = refl
assoc-* + + - = refl
assoc-* + - + = refl
assoc-* + - - = refl
assoc-* - + + = refl
assoc-* - + - = refl
assoc-* - - + = refl
assoc-* - - - = refl

comm-* : Commutative _*_
comm-* + + = refl
comm-* + - = refl
comm-* - + = refl
comm-* - - = refl

semigroup-*+ : Semigroup _*_
semigroup-*+ = record { assoc = assoc-* }

monoid-*+ : Monoid _*_ +
monoid-*+ = record
    { isSemigroup = semigroup-*+
    ; identity  = record { left-id  = +*x≡x
                         ; right-id = x*+≡x } }

ind-Sign : {C : Sign → Set} → C + → C - → (x : Sign) → C x
ind-Sign x _ + = x
ind-Sign _ y - = y

rec-Sign : {C : Set} → C → C → Sign → C
rec-Sign = ind-Sign
