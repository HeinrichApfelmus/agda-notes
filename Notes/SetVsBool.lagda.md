# Set VS Bool

01 January 2024,
by Heinrich Apfelmus,
[CC-BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/)

# Overview

When reasoning about Haskell programs using [agda2hs][], we can distinguish
two usage patterns of Agda:

* Agda, used to embed Haskell code — the "theory"
* Agda, used as logic to reason about Haskell — the "metatheory".

In other words, the "theory" is meant to be transpiled to Haskell code,
while the "methatheory" is used to prove statements about that Haskell code.
The beauty of a dependent type theory like Agda is that it can accomodate
both usage patterns at the same time.

However, when reasoning about Haskell programs, both the "theory" and the "metatheory" can express logical predicates and connectives — Haskell has `Bool` for logical truth values, whereas Agda uses `Set` for logical propositions. Which one should we use?

In this note, we compare the use of `Set` against `Bool` for a specific example.

In particular, we consider the following statement: If all elements of a list have a given property, then given a value `x` and a proof that `x` is an element of the list, we can conclude that `x` has this property has well. There are two ways to express the precondition:

* `Bool` — The property is modeled by a function `p : a → Bool`, and the fact that all list elements have this property is modeled by the type `all p xs ≡ True`, where `all : (a → Bool) → List a → Bool` is the function known from the Haskell Prelude.
* `Set` — The property is modeled by a dependent type `P : a → Set`, and the fact that all list elements have this property is modeled by an inductive type `data All (P : a → Set) : List a → Set`.

Both ways of modeling the statement have advantages and disadvantages:

1. The `Bool` way gives us a program `all` that can be evaluated within Haskell. In contrast, the `Set` way gives us a predicate `All` in the metatheory only. Importantly, in order to define the predicate `All`, we have to essentially duplicate the definition of `all` — we need to reflect it in the metatheory.
2. The `Set` way may be easier to use in proofs, because `All` is tailored to Agda in a way that `all` is not.

In other words, we can consider this as a trade-off: Does the cost of duplicating the predicate `all` as `All` in the metatheory yield a benefit in the simplification of proofs?

The present note investigates this trade-off.

We will come to the following conclusions:

* Viewed from the perspecitve of the Curry-Howards-isomorphism, the `Bool` way can be **as concise** as the `Set` way — we can add introduction and elimination rules for predicates of the form `(≡ True)` that mirror the `Set` rules*.
* The use of computed equality `==` as opposed to propositional equality `≡` adds some verbosity. However, for abstract data types, we may have to use setoids as opposed to `≡`, and I suspect that the trade-off may no longer disfavor `==`.
* Pattern matching in Agda is an additional rewriting / automatic proof-finding mechanism that is not available in plain type theory. This mechanism does yield additional simplifications — it is preferable to writing proof terms in plain lambda calculus. However, it is also independent of the `Set` VS `Bool` question.
    * The termination checker is instrumental to writing proofs by induction.
    * Fully dependent pattern matching can potentially perform large rewrites or automatically remove unreachable cases. I am not sure how useful that is in general, however, as more complex examples are also harder to control / reason about.
    * Perhaps allowing computation in pattern synonyms could bring `Bool` on par with `Set` — as indicated, the proof terms mirror each other.

\* I have ignored the verbosity of writing `p x ≡ True` as opposed to `P x`, as the former notation can be shortened once one commits to the `Bool` way, e.g. by writing `T (p x)` with `T : Bool → Set`. For the purpose of exposition, we use `p x ≡ True` as it is easier to understand.

  [agda2hs]: https://github.com/agda/agda2hs/


## Imports

```agda
{-# OPTIONS --erasure #-}

module SetVsBool where

open import Haskell.Prelude hiding (all; any; elem; All)
```

# All, Any and list membership

In this section, we compare the formulation of the statement and its preconditions, both for the `Set` way and the `Bool` way. 

## Set

Our goal is to prove the following statement:

    all-elem-satisfy-Set
      : ∀ (P  : a → Set)
          (xs : List a)
      → All P xs
      → ∀ (x : a) → x ∈ xs → P x

which states that "Given a predicate `P` and a list `xs`, if all elements of the list satisfy the predicate `P`, then given a value `x` and a proof `x ∈ xs` that this value is contained in the list, it follows that the value also satisfies `P`." This statement is useful when we have a list whose elements satisfy `P` by construction, and we later,  at runtime, discover that a value `x` is a member of the list — then we can upgrade our knowledge about list membership to the fact that `P` holds.

We define the predicate `All` as an inductive data type, by giving two introduction rules:

```agda
data All (P : a → Set) : List a → Set where
  Nil  : All P []
  Also : ∀ {x xs} → P x → All P xs → All P (x ∷ xs) 
```

The rule `Nil` states that all elements of the empty list satisfy the predicate, while the rule `Also` states that the list satisfies the predicate if both the head and the tail of the list satisfy it.

We define list membership through a general predicate `Any` with two introduction rules:

```agda
data Any (P : a → Set) : List a → Set where
  Here  : ∀ {x xs} → P x      → Any P (x ∷ xs) 
  There : ∀ {x xs} → Any P xs → Any P (x ∷ xs)
```

In other words, `Any P xs` holds when we can exhibit at least one element (`Here`) of the list satisfies the predicate. A value `x` is a member of the list if there is any list element being equal to it:

```agda
_∈_ : a → List a → Set
_∈_ x = Any (x ≡_)
```

## Bool

In the `Bool` way, the statement that we want to prove looks slightly more verbose:

    all-elem-satisfy-Bool
      : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
          (p  : a → Bool)
          (xs : List a)
      → all p xs ≡ True
      → ∀ (x : a) → elem x xs ≡ True → p x ≡ True

In contrast to the previous statement in the metatheory, this statement only involves values that can be computed in Haskell. In particular, we have a constraint on `Eq` to compute equality for list membership, and we compare results of the functions `all`, `elem` and `any` to `True`.

The definition of `all` closely mirrors the definition `All` from the metatheory:

```agda
all : ∀ (p : a → Bool) → List a → Bool
all p [] = True
all p (x ∷ xs) = p x && all p xs
```

We have two cases, one case for the empty list, and one case for a nonempty list; the latter case is a logical conjunction of a statement about the head of the list and the tail of the list.

Again, we define list membership in terms of a function `any`, whose definition closely mirrors the definition of `Any`:

```agda
any : ∀ (p : a → Bool) → List a → Bool
any p [] = False
any p (x ∷ xs) = p x || any p xs
```

However, here, the two cases of `Any` correspond to the two branches of the `||` operator, and the first match of `any` does not occur in the definition of `Any`.

A value x is a member of the list if there is any list element being equal to it:

```agda
elem : ⦃ Eq a ⦄ → a → List a → Bool
elem x = any (_== x)
```

# General proof terms

In this section, we define various proof terms, i.e. introduction or elimination rules for logical connectives or properties.

## Set

As Agda provides the elimination rules for logical connectives in the form of pattern matching, there is little left for us to define.

However, we do need the substitution rule for equality `≡`:

```agda
subst : (P : a → Set) {x y : a} → x ≡ y → P x → P y
subst P refl z = z
```

## Bool

We can make the logical connectives `&&` and `||` on `Bool` as convenient to use as their constructive counterparts in `Set` by defining appropriate introduction and elimination rules. In other words, proof terms for `Bool` and `Set` variants will be mirror images of each other — and the main syntactic difference between those two will be Agda's support for pattern matching, which is better for the constructive logical connectives in `Set`.

The elimination rules for logical conjunction `&&` are

```agda
&&-fst : ∀ (x y : Bool) → (x && y) ≡ True → x ≡ True
&&-fst True True refl = refl

&&-snd : ∀ (x y : Bool) → (x && y) ≡ True → y ≡ True
&&-snd True True refl = refl
```

Compare this with the elimination rules for a pair:

```agda
×-fst : ∀ {x y : Set} → x × y → x
×-fst (x , y) = x

×-snd : ∀ {x y : Set} → x × y → y
×-snd (x , y) = y
```

The elimination rule for logical disjunction `||` corresponds to a case expression:

```agda
||-elim
  : ∀ (x y : Bool) → (x || y) ≡ True → (x ≡ True → c) → (y ≡ True → c) → c
||-elim True y refl l r = l refl
||-elim False True refl l r = r refl
```

Compare with the constructive counterpart:

```agda
Either-elim
  : ∀ {x y : Set} → Either x y → (x → c) → (y → c) → c
Either-elim (Left  x) l r = l x
Either-elim (Right y) l r = r y
```

We also need a substitution rule

```agda
subst'
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
  → (p : a → Bool) → (x y : a) → (x == y) ≡ True → p x ≡ True → p y ≡ True
subst' p x y eq px = trans (sym (cong p (equality x y eq))) px
```

# Proof of `all-elem-satisfy`

In this section, we now present the proofs of the statement we introduced in the beginning.

In both cases, we perform a proof by induction on the list `xs`.

In `Set`, we proceed as follows:

```agda
all-elem-satisfy-Set
  : ∀ (P  : a → Set)
      (xs : List a)
  → All P xs
  → ∀ (x : a) → x ∈ xs → P x
all-elem-satisfy-Set P (y ∷ ys) (Also Py _) x (Here x≡y) =
    subst P (sym x≡y) Py
all-elem-satisfy-Set P (y ∷ ys) (Also _ pall) x (There pelem) =
    all-elem-satisfy-Set P ys pall x pelem
```

In `Bool`, we proceed as follows

```agda
all-elem-satisfy-Bool
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
      (p  : a → Bool)
      (xs : List a)
  → all p xs ≡ True
  → ∀ (x : a) → elem x xs ≡ True → p x ≡ True
all-elem-satisfy-Bool p [] pall x ()
all-elem-satisfy-Bool p (y ∷ ys) pall x pelem =
  ||-elim _ _ pelem
    (λ here → subst' p y x here (&&-fst _ _ pall))
    (λ there → all-elem-satisfy-Bool p ys (&&-snd _ _ pall) x there)
```

The two proofs are remarkably similar! We first make a case distinction on list membership (pattern match for `Set`, `||-elim` for `Bool`) and then either perform a substitution to conclude the property for the value `x`, or proceed recursively.

Observations:

* In terms of proof terms, the `Bool` way is just as consise as the `Set` way, as the elimination rules mirror each other.
* The use of `==` is more verbose than the built-in propositional equality `≡`. However, this is partly due to the fact that `==` is a computable function in Haskell, while `≡` is a notion confined to the metatheory.
* Agda's pattern matching is helpful in both cases:
  * For `Set`, pattern matching makes it unnecessary to use the elimination rules as proof terms.
  * For `Set`, pattern matching recognizes that the case for the empty list can be omitted.
  * For `Bool`, pattern matching on the list is still helpful to structure the program.
  * For `Bool`, the termination checker is also instrumental to completing the proof by induction.

