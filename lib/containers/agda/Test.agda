{-# OPTIONS --erasure #-}

module Test where

open import Haskell.Prelude

open import Haskell.Data.Set using (member)

import Haskell.Data.Set as Set

{-----------------------------------------------------------------------------
    Helper lemmas
------------------------------------------------------------------------------}
||-sym : ∀ (a b : Bool) → (a || b) ≡ (b || a)
||-sym False False = refl
||-sym False True = refl
||-sym True False = refl
||-sym True True = refl

{-----------------------------------------------------------------------------
    Test of Data.Set
------------------------------------------------------------------------------}
module Prop {a : Set} {{iOrd : Ord a}} where
  --
  union-sym
    : ∀ (x : a) (s1 s2 : Set.ℙ a)
    → member x (Set.union s1 s2)
      ≡ member x (Set.union s2 s1)
  --
  union-sym x s1 s2 =
    begin
      member x (Set.union s1 s2)
    ≡⟨ Set.Prop.member-union _ _ _ ⟩
      (member x s1 || member x s2)
    ≡⟨ ||-sym (member x s1) (member x s2) ⟩
      (member x s2 || member x s1)
    ≡⟨ sym (Set.Prop.member-union _ _ _) ⟩
      member x (Set.union s2 s1)  
    ∎
