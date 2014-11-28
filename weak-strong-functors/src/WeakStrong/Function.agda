------------------------------------------------------------------------
-- The Weak and the Strong: Functors
--
--
------------------------------------------------------------------------

module WeakStrong.Function where

infixr 9 _∘_

id : {A : Set} → A → A
id x = x

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
g ∘ f = λ x → g (f x)
