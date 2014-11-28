------------------------------------------------------------------------
-- The Weak and the Strong: Functors
--
-- Lists
------------------------------------------------------------------------

module WeakStrong.Data.List where

infixr 5 _∷_

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A
