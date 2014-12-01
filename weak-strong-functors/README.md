The Weak and the Strong: Functors
=================================

> > Let the weak say, I am strong.

> Or not.

When programming in functional languages such as Agda and Haskell, we
usually define functions and then show that they satisfy a given
specification. To that effect, we can

- define functions with a weak specification and then show that they
  satisfy it via companion tests or proofs, or

- define functions with a strong specification which they satisfy by
  definition.

As an example, let's consider the type signature of the `map` function
in Haskell:

```haskell
map :: (a -> b) -> [a] -> [b]
```

The `map` function applies a function to each element of a list.

According to the documentation, `map f xs` is the list obtained by applying
`f` to each element of `xs`, that is,

```haskell
map f [x1, x2, ...] == [f x1, f x2, ...]
```

Together, the type signature and the informal description of the
function are a weak specification of mapping over lists. We could
define several map functions which satisfy the previous specification,
but they're not the regular map function. With this in mind, we can
think of the Functor type class, which generalizes the map function.
The Functor class is used for types that can be mapped over.

```haskell
class Functor f where
  fmap :: (a -> b) -> f a -> f b
```

This is still a weak specification, but the documentation says that
"instances of Functor should satisfy the following laws:"

```haskell
fmap id      == id
fmap (g . f) == fmap g . fmap f
```

Which guarantee that f and fmap are actually a functor. In Haskell, we
can test these or prove (by hand) in order to get a weak specification
(doing this is still the programmer's responsibility).

Let's consider the [] (or list) functor, which is the list type
constructor and the map function we discussed earlier.

```haskell
instance Functor [] where
  fmap _ []     = []
  fmap f (x:xs) = f x : fmap f xs
```

In Haskell, this is not the only way to define a type checking
instance, but we could prove the laws by hand or test them. In fact,
the laws hold for this instance, but they're not part of the
specification. In Agda, we can have the same weak specification:

```agda
record RawFunctor (F : Set → Set) : Set₁ where
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
```

And We can define map as follows:

```agda
fmap : ∀ {A B} → (A → B) → List A → List B
fmap _ []       = []
fmap f (x ∷ xs) = f x ∷ fmap f xs
```

And our functor instance is just the List type constructor and the
fmap function.

```agda
rawFunctor : RawFunctor List
rawFunctor = record { fmap = fmap }
```

We could prove as companion lemmas that the laws hold. In fact, that's
what Agda's standard library does. But we can also have a strong
specification of functors, so that a functor is not just a type
constructor and an fmap function, but also proofs of both laws.

```agda
record Functor (F : Set → Set) : Set₁ where
  field
    fmap    : ∀ {A B} → (A → B) → F A → F B

    fmap-id : ∀ {A} (fx : F A) → fmap id fx ≡ fx

    fmap-∘  : ∀ {A B C} {f : A → B} {g : B → C}
              (fx : F A) → fmap (g ∘ f) fx ≡ fmap g (fmap f fx)
```

Now, our instance for the List functors contains both proofs:

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

There is no way to define a functor which is not a functor (in this
case, we know this is true because the specification comes from
category theory. In other cases, of course, we could still have wrong
specification or something like that.) Now our definition of the list
functor contains a proof of the fact that it is in fact a functor in
the mathematical sense.

This is close to Adam Chlipala's idea of a certified program, which is
the idea of a certificate or formal mathematical artifact proving that
a program meets its specification. In this way, the type of these
functions are more explicit about their behavior.

According to Adam Chlipala, the idea of a certified program has to do
with the idea of a certificate or formal mathematical artifact proving
that a program meets its specification.

According to Yves Bertot and Pierre Casterán, adding proof arguments
to functions makes it possible to make the type of these functions
more explicit about their behavior.

So?

[1] Bertot, Yves and Pierre Casterán

[12]: https://github.com/jpvillaisaza/weak-strong/tree/master/weak-strong-functors/
