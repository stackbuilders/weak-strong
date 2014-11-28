The Weak and the Strong: Functors
=================================

> > Let the weak say, I am strong.

> Or not.

```haskell
map :: (a -> b) -> [a] -> [b]
```

```haskell
class Functor f where
  fmap :: (a -> b) -> f a -> f b
```

```haskell
fmap id = id
```

```haskell
fmap (g . f) = fmap g . fmap f
```

```haskell
instance Functor [] where
  fmap _ []     = []
  fmap f (x:xs) = f x : fmap f xs
```

```agda
record RawFunctor (F : Set → Set) : Set₁ where
  field
    fmap : {A B : Set} → (A → B) → F A → F B
```

```agda
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A
```

```agda
functor : RawFunctor List
functor = record { fmap = fmap }
  where
    fmap : {A B : Set} → (A → B) → List A → List B
    fmap _ []       = []
    fmap f (x ∷ xs) = f x ∷ fmap f xs
```
