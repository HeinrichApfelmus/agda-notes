{-# OPTIONS --erasure #-}

module Haskell.Data.Foldable.Law.Def
    {-
    ; IsLawfulFoldable
    ; foldMap-toList-universal
    -} where

open import Haskell.Prelude
open import Haskell.Reasoning

open import Haskell.Data.Monoid

{-----------------------------------------------------------------------------
    IsLawfulFoldable
    Definition
------------------------------------------------------------------------------}

record IsLawfulFoldable
    (t : Set → Set)
    {{iFoldable : Foldable t}}
    : Set₁
  where
    field
      -- Commutes with monoid morphisms
      foldMap-morphism
        : ∀ {m1 m2 : Set} {{iMonoid1 : Monoid m1}} {{iMonoid2 : Monoid m2}}
            (g : MonoidMorphism m1 {{iMonoid1}} m2 {{iMonoid2}})
            (f : a → m1)
            (xs : t a)
        → getMonoidMorphism g (foldMap {{iFoldable}} {{iMonoid1}} f xs)
          ≡ foldMap {{iFoldable}} {{iMonoid2}} (getMonoidMorphism g ∘ f) xs

      -- Definitions of the other functions
      foldr-foldMap
        : ∀ (f : a → b → b) (z : b) (xs : t a)
        → foldr f z xs
            ≡ foldMap {{iFoldable}} {{MonoidEndo}} f xs z

      foldl-foldMap
        : ∀ (f : b → a → b) (z : b) (xs : t a)
        → foldl f z xs
            ≡ foldMap {{iFoldable}} {{MonoidEndoᵒᵖ}} (flip f) xs z

      any-foldMap
        : ∀ (p : a → Bool) (xs : t a)
        → any p xs ≡ foldMap {{iFoldable}} {{MonoidDisj}} p xs

      all-foldMap
        : ∀ (p : a → Bool) (xs : t a)
        → all p xs ≡ foldMap {{iFoldable}} {{MonoidConj}} p xs

      null-any
        : ∀ (xs : t a)
        → null xs ≡ all (const False) xs

      elem-any
        : ∀ {{_ : Eq a}} (x : a) (xs : t a)
        → elem x xs ≡ any (x ==_) xs

      toList-foldMap
        : ∀ (xs : t a)
        → toList xs ≡ foldMap {{iFoldable}} (λ x → x ∷ []) xs

      sum-foldMap
        : ∀ {{_ : Num a}} (xs : t a)
        → sum xs ≡ foldMap {{iFoldable}} {{MonoidSum}} id xs

      product-foldMap
        : ∀ {{_ : Num a}} (xs : t a)
        → product xs ≡ foldMap {{iFoldable}} {{MonoidProduct}} id xs

      length-foldMap
        : ∀ (xs : t a)
        → length xs ≡ foldMap {{iFoldable}} {{MonoidSum}} (const 1) xs
  
open IsLawfulFoldable ⦃ ... ⦄ public

{-----------------------------------------------------------------------------
    IsLawfulFoldable
    toList is universal
------------------------------------------------------------------------------}

private
  foldMapList : ⦃ Monoid b ⦄ → (a → b) → List a → b
  foldMapList = foldMap

  foldMapList-singleton
    : ∀ ⦃ _ : Monoid b ⦄
        ⦃ _ : IsLawfulMonoid b ⦄
        (f : a → b)
        (x : a)
    → (foldMapList f ∘ (λ x → x ∷ [])) x ≡ f x
  foldMapList-singleton {{_}} {{isLawfulMonoid}} f x
    = rightIdentity isLawfulMonoid (f x)

{- Universal property of Foldable

It's always sufficient to prove something about foldMap
for the free monoid (List a).
-}
foldMap-toList-universal
    : ∀ {{iMonoid : Monoid b}}
        {{isLawfulMonoid : IsLawfulMonoid b}}
        {{iFoldable : Foldable t}}
        {{isLawfulFoldable : IsLawfulFoldable t}}
        (f : a → b)
        (xs : t a)
    → foldMap {{iFoldable}} f xs
    ≡ foldMap {{iFoldableList}} f (toList xs)
--
foldMap-toList-universal f xs =
  begin
    foldMap (λ x → f x) xs
  ≡⟨ cong (λ g → foldMap g xs) (sym (ext (foldMapList-singleton f))) ⟩
    foldMap (foldMapList f ∘ (λ x → x ∷ [])) xs
  ≡⟨  sym (foldMap-morphism (initialMorphismList f) (λ x → x ∷ []) xs) ⟩
    foldMap f (foldMap (λ x → x ∷ []) xs)
  ≡⟨ cong (foldMap f) (sym (toList-foldMap xs)) ⟩
    foldMap f (toList xs)
  ∎
