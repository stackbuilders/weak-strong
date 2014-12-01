The Weak and the Strong: Functors
=================================

> > Let the weak say, I am strong.

> Or not.

When programming in functional languages such as [Agda][agda] and
[Haskell][haskell], we usually define functions and then show that
they satisfy a given specification. To that effect, we can

- define functions with a weak specification and then show that they
  satisfy it via companion tests or proofs, or

- define functions with a strong specification which they satisfy by
  definition.

As an example, let's consider the `Functor` type class in Haskell,
which is used for types that can be mapped over:

```haskell
class Functor f where
  fmap :: (a -> b) -> f a -> f b
```

Instances of `Functor` should satisfy the following laws:

```haskell
fmap id      == id
fmap (g . f) == fmap g . fmap f
```

Declaring an instance of the `Functor` type class and then testing or
proving these laws is how we define a functor with a weak
specification in Haskell.

For example, this is the instance of `Functor` for lists, which
satisfies the functor laws:

```haskell
instance Functor [] where
  fmap _ []     = []
  fmap f (x:xs) = f x : fmap f xs
```

Now, defining functions with a strong specification usually relies on
dependent types, which is why we'll take a look at functors in Agda:

```agda
record RawFunctor (F : Set → Set) : Set₁ where
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
```

Declaring a `RawFunctor` record and then proving the functor laws is
how we define a functor with a weak specification in Agda. In fact,
this is how functors are defined in the Agda standard library right
now.

For example, this is the `RawFunctor` record for lists, which
satisfies the functor laws:

```agda
rawFunctor : RawFunctor List
rawFunctor = record { fmap = fmap }
```

where

```agda
fmap : ∀ {A B} → (A → B) → List A → List B
fmap _ []       = []
fmap f (x ∷ xs) = f x ∷ fmap f xs
```

But we can include the functor laws in the definition of functors:

```agda
record Functor (F : Set → Set) : Set₁ where
  field
    fmap    : ∀ {A B} → (A → B) → F A → F B

    fmap-id : ∀ {A} (fx : F A) → fmap id fx ≡ fx

    fmap-∘  : ∀ {A B C} {f : A → B} {g : B → C}
              (fx : F A) → fmap (g ∘ f) fx ≡ fmap g (fmap f fx)
```

Thus, declaring a `Functor` record is how we define a functor with a
strong specification in Agda.

For instance, here's the `Functor` record for lists:

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

This is but one example of weak and strong specifications. Of course,
strong specifications are more complex than weak ones, but they're
also more explicit about the behavior of our functions and closer to
the idea of having a certificate of the correctness of our programs.

What do you think?

---

For more on weak and strong specifications, and dependent types, see,
for instance, Adam Chlipala's [Certified Programming with Dependent
Types][cpdt], Yves Bertot and Pierre Casterán's [Interactive Theorem
Proving and Program Development][coqart], and Ana Bove and Peter
Dybjer's [Dependent Types at Work][dtw].

(For the Agda and Haskell code, see
<https://github.com/jpvillaisaza/weak-strong/tree/master/weak-strong-functors/>.)

[agda]:    http://wiki.portal.chalmers.se/agda/
[coqart]:  http://www.labri.fr/perso/casteran/CoqArt/
[cpdt]:    http://adam.chlipala.net/cpdt/
[dtw]:     http://link.springer.com/chapter/10.1007/978-3-642-03153-3_2
[haskell]: http://www.haskell.org/
