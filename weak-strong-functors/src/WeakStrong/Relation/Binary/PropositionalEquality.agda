------------------------------------------------------------------------
-- The Weak and the Strong: Functors
--
--
------------------------------------------------------------------------

module WeakStrong.Relation.Binary.PropositionalEquality where

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
