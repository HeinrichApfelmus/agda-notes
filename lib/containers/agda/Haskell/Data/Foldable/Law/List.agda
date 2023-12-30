{-# OPTIONS --erasure #-}

module Haskell.Data.Foldable.Law.List
    {-
    ; isLawfulFoldableList
    -}
    where

open import Haskell.Prelude
open import Haskell.Reasoning

open import Haskell.Data.Bool as Bool
open import Haskell.Data.Monoid
open import Haskell.Data.Foldable.Law.Def

{-----------------------------------------------------------------------------
    IsLawfulFoldable List
------------------------------------------------------------------------------}
private
  foldMapList : ⦃ Monoid b ⦄ → (a → b) → List a → b
  foldMapList = foldMap

@0 foldMapList-morphism
  : ∀ {m1 m2 : Set} {{iMonoid1 : Monoid m1}} {{iMonoid2 : Monoid m2}}
      (gm : MonoidMorphism m1 {{iMonoid1}} m2 {{iMonoid2}})
      (f : a → m1)
      (xs : List a)
  → getMonoidMorphism gm (foldMapList {{iMonoid1}} f xs)
    ≡ foldMapList{{iMonoid2}} (getMonoidMorphism gm ∘ f) xs
foldMapList-morphism gm f [] = MonoidMorphism.comm-mempty gm
foldMapList-morphism gm f (x ∷ xs) =
  begin
    g (f x <> foldMapList f xs)
  ≡⟨  MonoidMorphism.comm-<> gm (f x) (foldMapList f xs) ⟩
    g (f x) <> (g (foldMapList f xs))
  ≡⟨ cong (g (f x) <>_) (foldMapList-morphism gm f xs) ⟩
    (g ∘ f) x <> foldMapList (g ∘ f) xs
  ∎
  where
    g = getMonoidMorphism gm


instance
  @0 isLawfulFoldableList : IsLawfulFoldable List
  isLawfulFoldableList .foldMap-morphism = foldMapList-morphism
  isLawfulFoldableList .foldr-foldMap f z xs = refl
  isLawfulFoldableList .foldl-foldMap f z xs = refl
  isLawfulFoldableList .any-foldMap p xs = refl
  isLawfulFoldableList .all-foldMap p xs = refl
  isLawfulFoldableList .null-any xs = refl
  isLawfulFoldableList .elem-any x xs = refl
  isLawfulFoldableList .toList-foldMap [] = refl
  isLawfulFoldableList .toList-foldMap (x ∷ xs) =
    begin
      x ∷ toList xs
    ≡⟨ cong (x ∷_) (toList-foldMap {{iFoldableList}} {{isLawfulFoldableList}} xs) ⟩
      x ∷ foldMapList (λ y → y ∷ []) xs
    ≡⟨⟩
      (x ∷ []) <> foldMapList (λ y → y ∷ []) xs
    ∎
  isLawfulFoldableList .sum-foldMap xs = refl
  isLawfulFoldableList .product-foldMap xs = refl
  isLawfulFoldableList .length-foldMap xs = refl

