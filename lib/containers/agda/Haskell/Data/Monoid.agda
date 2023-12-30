{-# OPTIONS --erasure #-}

module Haskell.Data.Monoid
    {-
    ; instance
      ; isLawfulSemigroupConj
      ; isLawfulMonoidConj
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

