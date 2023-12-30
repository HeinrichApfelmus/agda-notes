{-# OPTIONS --erasure #-}

module Haskell.Data.Bool
    {-
    ; Prop
      ; Prop.||-sym
      ; Prop.deMorgan-&&-||
      ; Prop.deMorgan-||-&&
    -}
    where

open import Haskell.Prelude

{-----------------------------------------------------------------------------
    Data.Bool
    Operations
------------------------------------------------------------------------------}

-- | Classical implication.
_==>_ : Bool → Bool → Bool
_==>_ x y = not x || y

{-----------------------------------------------------------------------------
    Data.Bool
    Properties
------------------------------------------------------------------------------}

module Prop where

  --
  ==>-ponens
    : ∀ (x y : Bool)
    → x ≡ True → (x ==> y ≡ True) → y ≡ True
  --
  ==>-ponens True True refl refl = refl 

  --
  ||-sym
    : ∀ (a b : Bool)
    → (a || b) ≡ (b || a)
  --
  ||-sym False False = refl
  ||-sym False True = refl
  ||-sym True False = refl
  ||-sym True True = refl

  --
  deMorgan-&&-||
    : ∀ (a b : Bool)
    → not (a && b) ≡ (not a || not b)
  --
  deMorgan-&&-|| False y = refl
  deMorgan-&&-|| True y = refl

  --
  deMorgan-||-&&
    : ∀ (a b : Bool)
    → not (a || b) ≡ (not a && not b)
  --
  deMorgan-||-&& False y = refl
  deMorgan-||-&& True y = refl