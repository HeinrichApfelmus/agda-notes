{-# OPTIONS --erasure #-}

module Haskell.Data.Foldable
    {-
    ; fold
    -}
    where

open import Haskell.Prelude

{-----------------------------------------------------------------------------
    Data.Foldable
    Operations
------------------------------------------------------------------------------}

fold : ∀ {{_ : Foldable t}} {{_ : Monoid a}} → t a → a
fold c = foldMap (λ x → x) c
