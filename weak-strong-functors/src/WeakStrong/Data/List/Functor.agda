------------------------------------------------------------------------
-- The Weak and the Strong: Functors
--
-- The List functor
------------------------------------------------------------------------

module WeakStrong.Data.List.Functor where

open import WeakStrong.Category.Functor
open import WeakStrong.Data.List
open import WeakStrong.Function
open import WeakStrong.Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- The List fmap function

fmap : ∀ {A B} → (A → B) → List A → List B
fmap _ []       = []
fmap f (x ∷ xs) = f x ∷ fmap f xs

------------------------------------------------------------------------
-- The List (weak) functor

rawFunctor : RawFunctor List
rawFunctor = record { fmap = fmap }

------------------------------------------------------------------------
-- The List (strong) functor

functor : Functor List
functor = record { fmap = fmap ; fmap-id = fmap-id ; fmap-∘ = fmap-∘ }
  where
    fmap-id : {A : Set} (xs : List A) → fmap id xs ≡ xs
    fmap-id []       = refl
    fmap-id (x ∷ xs) = cong (_∷_ x) (fmap-id xs)

    fmap-∘ : ∀ {A B C} {f : A → B} {g : B → C}
             (xs : List A) → fmap (g ∘ f) xs ≡ fmap g (fmap f xs)
    fmap-∘             []       = refl
    fmap-∘ {f = f} {g} (x ∷ xs) = cong (_∷_ (g (f x))) (fmap-∘ xs)
