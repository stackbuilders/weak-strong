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

Certainly, declaring the instance of `Functor` for lists is not
enough. We need to test or prove that it satisfies the functor laws,
but we're not gonna do that yet.

In order to see that thinking of the functor laws is important, let's
consider an alternative instance of `Functor` for lists:

```haskell
instance Functor [] where
  fmap _ _ = []
```

Even though this is a valid instance of `Functor`, it's not really a
functor because it violates the functor laws. With a weak
specification, ensuring that the laws hold is our responsibility, but
we could use a strong specification in which we define a functor and,
at the same time, prove that it is indeed a functor.

Now, defining functions with a strong specification usually relies on
[dependent types](http://en.wikipedia.org/wiki/Dependent_type) or
types that depend on elements of other types, which is why we'll take
a look at functors in Agda:

```agda
record RawFunctor (F : Set → Set) : Set₁ where
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
```

Here, we use record types for Haskell type classes, so the
`RawFunctor` record is equivalent to the `Functor` type class in
Haskell.

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

Again, we have to prove that `List` and `fmap` satisfy the functor
laws, but we're not gonna do that yet.

However, we can include the functor laws in the definition of functors
so that there's no way to define a functor which is not a functor:

```agda
record Functor (F : Set → Set) : Set₁ where
  field
    fmap    : ∀ {A B} → (A → B) → F A → F B

    fmap-id : ∀ {A} (fx : F A) → fmap id fx ≡ fx

    fmap-∘  : ∀ {A B C} {f : A → B} {g : B → C}
              (fx : F A) → fmap (g ∘ f) fx ≡ fmap g (fmap f fx)
```

Here, `fmap-id` and `fmap-∘` are fields just like `fmap`. Given an
element `fx` of `F A`, `fmap-id fx` and `fmap-∘ fx` are proofs of the
first and second functor laws, respectively. Additionally, `≡` is just
a (dependent) type representing propositional (intensional) equality.

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

We prove both laws by induction and use the fact that propositional
equality is a reflexive and congruence relation. Even if the proofs'
details are not clear, what matters now is that this definition of the
`Functor` record for lists satisfies our specification because it
contains actual proofs of the functor laws. Moreover, it's the only
way to define a type checking `Functor` record for lists.

This is but one example of weak and strong specifications. Of course,
strong specifications are more complex than weak ones, but they're
also more explicit about the behavior of our functions and closer to
the idea of having a certificate of the correctness of our programs.

What do you think?

---

(Based on a homework for [Dependently Typed Functional
Languages][dtfl], chapter 9 of Yves Bertot and Pierre Casterán's
[Interactive Theorem Proving and Program Development][coqart], some of
Adam Chlipala's ideas on [Certified Programming with Dependent
Types][cpdt], section 6 of Ana Bove and Peter Dybjer's [Dependent
Types at Work][dtw], and section 3 of the [Typeclassopedia][tc].)

(You can get the code at
<https://github.com/jpvillaisaza/weak-strong/tree/master/weak-strong-functors/>.)

[agda]:    http://wiki.portal.chalmers.se/agda/
[coqart]:  http://www.labri.fr/perso/casteran/CoqArt/
[cpdt]:    http://adam.chlipala.net/cpdt/
[dtfl]:    http://www1.eafit.edu.co/asicard/courses/dtfl-CB0683/
[dtw]:     http://link.springer.com/chapter/10.1007/978-3-642-03153-3_2
[haskell]: http://www.haskell.org/
[tc]:      https://www.haskell.org/haskellwiki/Typeclassopedia
