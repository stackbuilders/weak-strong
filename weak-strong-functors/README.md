The Weak and the Strong: Functors
=================================

> > Let the weak say, I am strong.

> Or not.

Two approaches:

- Weak specification. Define the functions with a weak specification
  and then add companion lemmas. According to Bove and Dybjer, this
  approach is sometimes called external programming logic: we write a
  program in an ordinary type system and afterwards we prove a
  property of it, so the property is just a logical "comment".

- Strong specification. The type of the function directly states that
  the output is the combination of a value and a proof. In this
  approach, we also say that we produce a well-specified function, and
  we usually rely on dependent types. According to Bove and Dybjer,
  this approach is sometimes called integrated or internal programming
  logic: the logic is integrated with the program.

  In both cases, we're using Agda as a programming logic, we use the
  system to prove properties of our programs.

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

According to Adam Chlipala, the idea of a certified program has to do
with the idea of a certificate or formal mathematical artifact proving
that a program meets its specification.

According to Yves Bertot and Pierre Casterán, adding proof arguments
to functions makes it possible to make the type of these functions
more explicit about their behavior.

[12]: https://github.com/jpvillaisaza/weak-strong/tree/master/weak-strong-functors/
