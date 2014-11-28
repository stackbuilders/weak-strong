------------------------------------------------------------------------
-- The Weak and the Strong: Functors
--
-- The Maybe functor
------------------------------------------------------------------------

module WeakStrong.Data.Maybe.Functor where

open import WeakStrong.Category.Functor
open import WeakStrong.Data.Maybe
open import WeakStrong.Function
open import WeakStrong.Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- The Maybe fmap function

fmap : ∀ {A B} → (A → B) → Maybe A → Maybe B
fmap _ nothing  = nothing
fmap f (just x) = just (f x)

------------------------------------------------------------------------
-- The Maybe (weak) functor

rawFunctor : RawFunctor Maybe
rawFunctor = record { fmap = fmap }

------------------------------------------------------------------------
-- The Maybe (strong) functor

functor : Functor Maybe
functor = record { fmap = fmap ; fmap-id = fmap-id ; fmap-∘ = fmap-∘ }
  where
    fmap-id : ∀ {A} (mx : Maybe A) → fmap id mx ≡ mx
    fmap-id nothing  = refl
    fmap-id (just _) = refl

    fmap-∘ : ∀ {A B C} {f : A → B} {g : B → C}
             (mx : Maybe A) → fmap (g ∘ f) mx ≡ fmap g (fmap f mx)
    fmap-∘ nothing  = refl
    fmap-∘ (just _) = refl
