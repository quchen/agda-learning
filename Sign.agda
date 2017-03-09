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
