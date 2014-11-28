------------------------------------------------------------------------
-- The Weak and the Strong: Functors
--
-- The Maybe functor
------------------------------------------------------------------------

module WeakStrong.Data.Maybe.Functor where

open import WeakStrong.Category.Functor
open import WeakStrong.Data.Maybe

functor : RawFunctor Maybe
functor = record { fmap = fmap }
  where
    fmap : {A B : Set} → (A → B) → Maybe A → Maybe B
    fmap _ nothing  = nothing
    fmap f (just x) = just (f x)
