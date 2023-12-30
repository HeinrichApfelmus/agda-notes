{-# OPTIONS --erasure #-}

module Haskell.Reasoning
    {-
    -} where

open import Axiom.Extensionality.Propositional public using
    ( Extensionality
    )

postulate 
  ext : ∀ {l1 l2} → Extensionality l1 l2
