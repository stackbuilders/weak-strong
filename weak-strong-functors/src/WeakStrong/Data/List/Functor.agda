------------------------------------------------------------------------
-- The Weak and the Strong: Functors
--
--
------------------------------------------------------------------------

module WeakStrong.Data.List.Functor where

open import WeakStrong.Category.Functor
open import WeakStrong.Data.List

functor : RawFunctor List
functor = record { fmap = fmap }
  where
    fmap : {A B : Set} → (A → B) → List A → List B
    fmap _ []       = []
    fmap f (x ∷ xs) = f x ∷ fmap f xs
