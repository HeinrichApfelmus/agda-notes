module Haskell.Data.Foldable.Law.Universal
    {-
    ; foldMap-toList-universal
    ; any-toList-universal
    ; all-toList-universal
    -}
    where

open import Haskell.Prelude

open import Haskell.Data.Monoid

open import Haskell.Data.Foldable.Law.Def
open import Haskell.Data.Foldable.Law.Def public using
    ( foldMap-toList-universal
    )
open import Haskell.Data.Foldable.Law.List

{-----------------------------------------------------------------------------
    IsLawfulFoldable
    Definition
------------------------------------------------------------------------------}

module _
    {{iFoldable : Foldable t}}
    {{isLawfulFoldable : IsLawfulFoldable t}}
  where
    --
    all-toList-universal
        : ∀ (p : a → Bool) (xs : t a)
        → all p xs ≡ all p (toList xs)
    --
    all-toList-universal p xs =
      begin
        all p xs
      ≡⟨ all-foldMap {{iFoldable}} {{isLawfulFoldable}} p xs ⟩
        foldMap {{iFoldable}} {{MonoidConj}} p xs
      ≡⟨ foldMap-toList-universal {{MonoidConj}} {{isLawfulMonoidConj}} p xs ⟩
        foldMap {{iFoldableList}} {{MonoidConj}} p (toList xs)
      ≡⟨⟩
        all p (toList xs)
      ∎

    --
    any-toList-universal
        : ∀ (p : a → Bool) (xs : t a)
        → any p xs ≡ any p (toList xs)
    --
    any-toList-universal p xs =
      begin
        any p xs
      ≡⟨ any-foldMap {{iFoldable}} {{isLawfulFoldable}} p xs ⟩
        foldMap {{iFoldable}} {{MonoidDisj}} p xs
      ≡⟨ foldMap-toList-universal {{MonoidDisj}} {{isLawfulMonoidDisj}} p xs ⟩
        foldMap {{iFoldableList}} {{MonoidDisj}} p (toList xs)
      ≡⟨⟩
        any p (toList xs)
      ∎

    --
    @0 elem-toList-universal
        : ∀ ⦃ _ : Eq a ⦄
            (x : a)
            (xs : t a)
        → elem x xs ≡ elem x (toList xs)
    --
    elem-toList-universal x xs =
      begin
        elem x xs
      ≡⟨ elem-any {{iFoldable}} {{isLawfulFoldable}} x xs ⟩
        any (x ==_) xs
      ≡⟨ any-toList-universal (x ==_) xs ⟩
        any (x ==_) (toList xs)
      ≡⟨ sym (elem-any {{_}} {{isLawfulFoldableList}} x (toList xs)) ⟩
        elem x (toList xs)
      ∎