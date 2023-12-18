# Notes on Agda

by Heinrich Apfelmus

License:

* CC-BY-SA for explanations on a per-file basis
* Apache-2.0 for source code

This repository collects various notes on [Agda][] and [agda2hs][].

My main motivation for using Agda is to prove properties of Haskell programs. Homotopy type theory and constructive mathematics are interesting, but not the focus here.

I wrote these notes to serve as a personal reference for various topics or techniques that I encountered. Perhaps they are useful to you.

Agda is a complex language, and in some instances, the interaction between different language features can be unpredictable. In particular, Agda has

* Pattern matching — This is the main feature that distinguishes Agda from (vanilla) Coq. Pattern matches make it straightforward to write definitions that would be hard to write using dependent eliminators, because mtaching can refine the types and values of multiple arguments at once. In Coq, you'd have to use a proof tactic.

* Implicit parameters `{}` — are infered by the compiler. Well, most of the time.

* Run-time erasure `@0` — highly useful when transliterating to Haskell using [Agda2hs][], because it helps erase proofs and we end up with simply-typed terms.

## Language setup

This repository contains a nix flake that includes

* [Agda][]
* [agda2hs][]
* Agda standard library, `Haskell.Prelude`

  [agda]: https://github.com/agda/agda
  [agda2hs]: https://github.com/agda/agda2hs

## TODO

* Proving with `case` expressions

* Equality of functions — Definitional, propositional and extensional equality
  * Extensionality is independent, but it's something that we definitely want.
  * https://github.com/agda/agda/issues/4590

* Fully verified implementation of `Data.Map` as binary tree.
* Setoid version of `Data.Map`

# References

Here is a list of texts that I found most useful when studying Agda. My focus is on proving Haskell programs correct, not so much on type theory.

## Introductions

I found the following introductions particularly lucid.

* Jesper Cockx, [Programming and Proving in Agda][cockx2023] (2023). — Highly recommended, the focus is on learning just enough Agda to prove Haskell programs correct. Builds on Graham Hutton's excellent, and deceptively simple book "Programming in Haskell".
* Xavier Leroy, [What is equality? From Leibniz to homotopy type theory][leroy2019] (2019). — At some point, you will find that the definitional equality `≡` is not enough; these talk slides give a nice overview of the state of the art on equality in type theory.
* Philip Wadler. [Programming language foundations in Agda][wadler2018] (2018). — The first chapter introduces many logical and type-theoretic concepts necessary for understanding Agda; the later chapters focus mostly on lambda calculi and are less relevant for proving Haskell programs correct.

## Details

Texts that cover more details of how Agda works.

* Ulf Norell's PhD thesis — Pattern matching. Holes and implicit parameters ("metavariables").
* Jesper Cockx — Pattern matching without axiom `K`. Needed for homotopy type theory models, where uniqueness of identify proofs (UIP) does not hold.


  [cockx2023]: https://github.com/jespercockx/agda-lecture-notes/blob/master/agda.pdf
  [leroy2019]: https://xavierleroy.org/CdF/2018-2019/10.pdf
  [wadler2018]: https://plfa.inf.ed.ac.uk/22.08/