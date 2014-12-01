The Weak and the Strong: Functors
=================================

> > Let the weak say, I am strong.

> Or not.

Two approaches:

- Weak specification. Define the function and then add companion lemmas.

  Sometimes called external programming logic: we write a program in
  an ordinary type system and afterwards we prove a property of it.
  The property is a logical "comment".

- Strong specification. The type of the function directly states that
  the input is a value of type A and that the output is the
  combination of a value b of type B and a proof that b satisfies R a
  b. We produce a well-specified function. We rely on dependent types.

  Sometimes called integrated or internal programming logic: the logic
  is integrated with the program.

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
    fmap : ∀ {A B} → (A → B) → F A → F B
```

```agda
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A
```

```agda
fmap : ∀ {A B} → (A → B) → List A → List B
fmap _ []       = []
fmap f (x ∷ xs) = f x ∷ fmap f xs
```

```agda
rawFunctor : RawFunctor List
rawFunctor = record { fmap = fmap }
```

```agda
record Functor (F : Set → Set) : Set₁ where
  field
    fmap    : ∀ {A B} → (A → B) → F A → F B

    fmap-id : ∀ {A} (fx : F A) → fmap id fx ≡ fx

    fmap-∘  : ∀ {A B C} {f : A → B} {g : B → C}
              (fx : F A) → fmap (g ∘ f) fx ≡ fmap g (fmap f fx)
```

```agda
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
```

The idea of a certified program has to do with the idea of a
certificate, or formal mathematical artifact proving that a program
meets its specification.

Adding proof arguments to functions makes it possible to make the type
of these functions more explicit about their behavior.

Of course, this is not a real world example. Should we let the weak
say, I am strong or not?

[12]: https://github.com/jpvillaisaza/weak-strong/tree/master/weak-strong-functors/
