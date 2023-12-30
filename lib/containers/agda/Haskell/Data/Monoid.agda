{-# OPTIONS --erasure #-}

module Haskell.Data.Monoid
    {-
    ; instance
      ; isLawfulSemigroupConj
      ; isLawfulMonoidConj
    ; MonoidMorphism
      ; deMorgan-&&-to-||
      ; deMorgan-||-to-&&
      ; initialMorphismList
    -}
    where

open import Haskell.Prelude hiding (f)
import Haskell.Data.Bool as Bool

{-----------------------------------------------------------------------------
    Lawful monoids
------------------------------------------------------------------------------}

instance 
  isLawfulSemigroupConj : IsLawfulSemigroup Bool {{super MonoidConj}}
  isLawfulSemigroupConj .associativity False y z = refl
  isLawfulSemigroupConj .associativity True y z = refl

instance
  isLawfulMonoidConj : IsLawfulMonoid Bool {{MonoidConj}}
  isLawfulMonoidConj .rightIdentity False = refl
  isLawfulMonoidConj .rightIdentity True = refl
  isLawfulMonoidConj .leftIdentity x = refl
  isLawfulMonoidConj .concatenation xs = lem1 xs
    where
      lem1
        : ∀ (xs : List Bool)
        → mconcat {{MonoidConj}} xs
          ≡ foldr (_<>_ {{super MonoidConj}}) (mempty {{MonoidConj}}) xs
      lem1 [] = refl
      lem1 (x ∷ xs) = cong (x &&_) (lem1 xs)


instance 
  isLawfulSemigroupDisj : IsLawfulSemigroup Bool {{super MonoidDisj}}
  isLawfulSemigroupDisj .associativity False y z = refl
  isLawfulSemigroupDisj .associativity True y z = refl

instance
  isLawfulMonoidDisj : IsLawfulMonoid Bool {{MonoidDisj}}
  isLawfulMonoidDisj .rightIdentity False = refl
  isLawfulMonoidDisj .rightIdentity True = refl
  isLawfulMonoidDisj .leftIdentity x = refl
  isLawfulMonoidDisj .concatenation xs = lem1 xs
    where
      lem1
        : ∀ (xs : List Bool)
        → mconcat {{MonoidDisj}} xs
          ≡ foldr (_<>_ {{super MonoidDisj}}) (mempty {{MonoidDisj}}) xs
      lem1 [] = refl
      lem1 (x ∷ xs) = cong (x ||_) (lem1 xs)


{-----------------------------------------------------------------------------
    Morphisms
------------------------------------------------------------------------------}
record MonoidMorphism
    a {{@0 dom : Monoid a}}
    b {{@0 co  : Monoid b}}
    : Set
  where
  field
    getMonoidMorphism : a → b

  f = getMonoidMorphism

  field
    @0 comm-mempty
        : f (mempty {{dom}}) ≡ mempty {{co}}
    @0 comm-<>
        : ∀ (x y : a)
        → f (_<>_ {{super dom}} x y) ≡ (_<>_ {{super co}} (f x) (f y))

open MonoidMorphism using (getMonoidMorphism) public

{-----------------------------------------------------------------------------
    Morphisms
    de Morgan's laws
------------------------------------------------------------------------------}

deMorgan-&&-to-||
  : MonoidMorphism Bool {{MonoidConj}} Bool {{MonoidDisj}}
deMorgan-&&-to-|| = record
  { getMonoidMorphism = not
  ; comm-mempty = refl
  ; comm-<> = Bool.Prop.deMorgan-&&-||
  }

deMorgan-||-to-&&
  : MonoidMorphism Bool {{MonoidDisj}} Bool {{MonoidConj}}
deMorgan-||-to-&& = record
  { getMonoidMorphism = not
  ; comm-mempty = refl
  ; comm-<> = Bool.Prop.deMorgan-||-&&
  }

{-----------------------------------------------------------------------------
    Morphisms
    de Morgan's laws
------------------------------------------------------------------------------}

private

  foldMapList : ⦃ Monoid b ⦄ → (a → b) → List a → b
  foldMapList = foldMap

  --
  lemma-++-comm
    : ∀ ⦃ _ : Monoid b ⦄
        ⦃ _ : IsLawfulMonoid b ⦄
        (f : a → b)
        (xs ys : List a)
    → foldMapList f (xs ++ ys)
      ≡ foldMapList f xs <> foldMapList f ys
  --
  lemma-++-comm {{_}} {{isLaw}} f [] ys =
    sym (IsLawfulMonoid.leftIdentity isLaw (foldMapList f ys))
  lemma-++-comm {{_}} {{isLaw}} f (x ∷ xs) ys =
    begin
      foldMapList f ((x ∷ xs) ++ ys)
    ≡⟨ cong (foldMapList f) (∷-++-assoc x xs ys) ⟩
      foldMapList f (x ∷ (xs ++ ys))
    ≡⟨⟩
      f x <> foldMapList f (xs ++ ys)
    ≡⟨ cong (λ y → f x <> y) (lemma-++-comm f xs ys)⟩
      f x <> (foldMapList f xs <> foldMapList f ys)
    ≡⟨ IsLawfulSemigroup.associativity (super isLaw) (f x) (foldMapList f xs) (foldMapList f ys) ⟩
      (f x <> foldMapList f xs) <> foldMapList f ys
    ≡⟨⟩
      foldMapList f (x ∷ xs) <> foldMapList f ys
    ∎

initialMorphismList
  : ∀ ⦃ iMonoid : Monoid b ⦄ ⦃ _ : IsLawfulMonoid b ⦄
  → (a → b)
  → MonoidMorphism (List a) b {{iMonoid}}
initialMorphismList f = record
  { getMonoidMorphism = foldMap f
  ; comm-mempty = refl
  ; comm-<> = lemma-++-comm f
  }
