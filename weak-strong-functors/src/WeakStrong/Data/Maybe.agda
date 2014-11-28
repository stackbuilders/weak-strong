------------------------------------------------------------------------
-- The Weak and the Strong: Functors
--
--
------------------------------------------------------------------------

module WeakStrong.Data.Maybe where

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : (x : A) → Maybe A
