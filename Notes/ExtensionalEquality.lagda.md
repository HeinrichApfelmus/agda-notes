# Extensional Equality

02 January 2024,
by Heinrich Apfelmus,
[CC-BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/)

This note describes the concept of **extensional equality**, and why the constructive Axiom of extensionality,

    postulate
      ext
        : ∀ {a b : Set} (f g : a → b)
        → (∀ (x : a) → f x ≡ g x) → f ≡ g

is worth postulating.

The main argument in favor of function extensionality is that without this axiom, **higher-order function** such as 

    filter : (a → Bool) → List a → List a

would need to be accompied with an additional specification and proof that they give the same result when applied to extensionally equal function arguments.

# Equality in Type Theory

Equality is a surprisingly subtle concept.

For example, in daily life, two things can be "the same", but they can also be "the exact same". When Alice and Bob read "the same" book, then this probably means that each of them reads their own copy of the book. However, if they read "the exact same" book, then there is only a single copy which Alice and Bob take turns reading.

Likewise, in type theory, there are several distinct notions of equality:

* Definitional equality
* Propositional equality, denoted `≡` in Agda
* Extensional equality

Definitional equality is very close to "the exact same", whereas extensional equality is more along the lines of "the same".

Before describing these notions in detail, we note that every notion of "equality" is an [equivalence relation][equiv], and vice versa. A relation `~` is said to be an equivalence relation iff it is

* reflexive, `refl : ∀ {x : a} → x ~ x`, and
* symmetric, `sym  : ∀ {x y : a} → x ~ y → y ~ x`, and
* transitive, `trans : ∀ {x y z : a} → x ~ y → y ~ z → x ~ z`.

For example, the `==` function familiar to Haskell programmers usually encodes an equivalence relation which is not propositional equality `≡`.

By the way, the key insight of [Homototpy Type Theory][hhot]
is to reinterpret propositional equality "x ≡ y" as a "path from x to y",
and then ask whether two paths can themselves be equal
— essentially asking about equality of equalities.
It turns out that, in some models of type theory,
this gives an axiomatization of homotopy theory that
does not require point-set topology.

  [hhot]: https://homotopytypetheory.org/book/
  [equiv]: https://en.wikipedia.org/wiki/Equivalence_relation

## Imports

```agda
open import Data.Bool
open import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

variable
  a b : Set
```

## Definitional equality

Two terms are **definitionally equal** if they have the same definition. For example,

* `x` is definitionally equal to `x`, because they are the same variable.
* `2` is definitially equal to `suc 1`, because the latter term is the definition of the former term.
* `λ x → x` is definitionally equal to `λ y → y`, because Agda is insensitive to renamings of variables.

Importantly, definitional equality is a **metatheoretical** concept — it cannot be observed from within Agda, only when talking **about** Agda.

## Propositional equality

Two terms are **propositionally equal** if they reduce to the same normal form.

Importantly, propositional equality is a concept that can be observed **within** Agda: Given two terms `x` and `y` that a propositionally equal, Agda will allow us to write a proof of this fact as `refl : x ≡ y`.

Examples:

```agda
ex1 : ∀ {x : a} → x ≡ x
ex1 = refl

ex2 : 2 + 2 ≡ 1 + 3
ex2 = refl

ex3 : false ≡ not true
ex3 = refl
```

The most important aspect of propositional equality is the law of **substitution**: Given a function `f : a → b` and two terms `x` and `y` that are propositionally equal, `x ≡ y`, then we can conclude that the function values `f x` and `f y` must also be propositionally equal:

```agda
cong : ∀ (f : a → b) → {x y : a} → x ≡ y → f x ≡ f y
cong f refl = refl
```

Likewise for any indexted type / predicate `P : a → Set`:

```agda
subst : ∀ (P : a → Set) {x y : a} → x ≡ y → P x → P y
subst P refl z = z
```

## Extensional Equality

Two functions `f`, `g` are **extensionally equal** if their results are propositionally equal for all arguments, that is `f x ≡ g x` for all arguments `x`. Formally, extensional equality is the statement `∀ (x : a) → f x ≡ g x`.

This notion equates functions which do not have the same normal form. For example, the functions

    f = λ x → 1 + x
    g = λ x → x + 1

give the same result for all `x`, because addition `+` is commutative. However, these functions have distinct definitions and distinct normal forms — the commutativity of `+` is not an apparent property of the terms. In practice, having two functions that are extensionally equal, but have very different source code is desired: One function `f` is a correct, but slow reference implementation, while the other function `g` is a difficult-to-prove-correct, but fast actual implementation.

In general, due to the halting problem, there is no notion of normal form for functions such that two functions that are extensionally equal have the same normal form, and vice versa.

For inductive data types, normal forms are appropriate for defining propositional equality. However, for functions, **extensional equality** is more appropriate. Therefore, we recommend to adopt the Axiom of extensionality,

```agda
postulate
  ext
    : ∀ {a b : Set} (f g : a → b)
    → (∀ (x : a) → f x ≡ g x) → f ≡ g
```

which postulates that propositional equality `≡` holds for functions that are extensionally equal. There are several reasons for this:

1. Definitional equality is particularly rare for functions in Agda.
2. The axiom ensures that **higher-order functions**, such as `map : (a → b) → List a → List b` or `filter : (a → Bool) → List a → List a` can only depend on the function results, not on its specific definition. Otherwise, `filter f` and `filter g` could, in principle, give different results depending on the source code of `f` and `g` — the fact that `filter` does not would have to be encoded and proven in a separate theorem.
3. Among axioms that can be added to type theory, extensionality of functions is uncontroversial — it is compatible with both [uniqueness of identity proofs (UID)][uid-ua] and the [univalence axiom][ua], two potential axioms which are incompatible.

Point 2 about higher-order functions is the most important one.

  [uid-ua]: https://cstheory.stackexchange.com/questions/50531/how-does-axiom-k-contradict-univalence
  [ua]: https://en.wikipedia.org/wiki/Homotopy_type_theory#The_univalence_axiom

Concering point 1 about definitional equality: Agda has made a few design choices that make definitional equality rare. For example, even though the following definitions appear to be visually the same,

```
f : Bool → Bool
f true = true
f false = false

g : Bool → Bool
g true = true
g false = false
```

Agda treats definitions by pattern matching as distinct, and will reject the proof

    eq : f ≡ g
    eq = refl

However, when defining the functions as lambda abstraction in terms of a single eliminator function `Bool-elim`,

```agda
Bool-elim
    : ∀ {P : Bool → Set}
    → (b : Bool)
    → P true → P false → P b
Bool-elim true x y = x
Bool-elim false x y = y

f' : Bool → Bool
f' = λ bib → Bool-elim bib true false

g' : Bool → Bool
g' = λ bob → Bool-elim bob true false
```

Agda will accept the following proof:

```agda
eq' : f' ≡ g'
eq' = refl
```