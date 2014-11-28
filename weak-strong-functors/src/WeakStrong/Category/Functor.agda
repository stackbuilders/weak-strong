------------------------------------------------------------------------
-- The Weak and the Strong: Functors
--
-- Functors
------------------------------------------------------------------------

module WeakStrong.Category.Functor where

open import WeakStrong.Function
open import WeakStrong.Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Functors (Weak)

record RawFunctor (F : Set → Set) : Set₁ where
  field
    fmap : ∀ {A B} → (A → B) → F A → F B

------------------------------------------------------------------------
-- Functors (Strong)

record Functor (F : Set → Set) : Set₁ where
  field
    fmap    : ∀ {A B} → (A → B) → F A → F B

    fmap-id : ∀ {A} (fx : F A) → fmap id fx ≡ fx

    fmap-∘  : ∀ {A B C} {f : A → B} {g : B → C}
              (fx : F A) → fmap (g ∘ f) fx ≡ fmap g (fmap f fx)
