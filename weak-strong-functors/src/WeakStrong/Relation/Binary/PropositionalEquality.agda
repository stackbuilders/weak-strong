------------------------------------------------------------------------
-- The Weak and the Strong: Functors
--
-- Propositional equality
------------------------------------------------------------------------

module WeakStrong.Relation.Binary.PropositionalEquality where

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

cong : ∀ {A B} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong _ refl = refl
