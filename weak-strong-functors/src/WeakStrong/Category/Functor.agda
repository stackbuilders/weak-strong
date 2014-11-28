------------------------------------------------------------------------
-- The Weak and the Strong: Functors
--
-- Functors
------------------------------------------------------------------------

module WeakStrong.Category.Functor where

record RawFunctor (F : Set → Set) : Set₁ where
  field
    fmap : {A B : Set} → (A → B) → F A → F B
