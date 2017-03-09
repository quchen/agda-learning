module Bool where

data Bool : Set where
    True : Bool
    False : Bool

data So : Bool → Set where
    Oh : So True
