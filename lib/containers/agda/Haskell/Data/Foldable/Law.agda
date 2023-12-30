module Haskell.Data.Foldable.Law
    {-
    ; isLawfulFoldableList
    -}
    where

open import Haskell.Prelude
open import Haskell.Reasoning

open import Haskell.Data.Bool
open import Haskell.Data.Monoid

open import Haskell.Data.Foldable.Law.Def public
open import Haskell.Data.Foldable.Law.List public
open import Haskell.Data.Foldable.Law.Universal public

{-----------------------------------------------------------------------------
    Various laws
------------------------------------------------------------------------------}
module _
    {{iFoldable : Foldable t}}
    {{isLawfulFoldable : IsLawfulFoldable t}}
  where

    --
    all-const-True
      : ∀ (xs : t a)
      → all (const True) xs ≡ True
    --
    all-const-True xs =
        trans
          (all-toList-universal (const True) xs)
          (all-const-True-list (toList xs))        
        
    --
    any-not-all
      : ∀ (p : a → Bool) (xs : t a)
      → not (any p xs) ≡ all (not ∘ p) xs
    --
    any-not-all p xs =
      begin
        not (any p xs)
      ≡⟨ cong not (any-foldMap p xs) ⟩
        not (foldMap {{iFoldable}} {{MonoidDisj}} p xs)
      ≡⟨ foldMap-morphism {{iFoldable}} {{isLawfulFoldable}} {{MonoidDisj}} {{MonoidConj}} deMorgan-||-to-&& p xs ⟩
        foldMap {{iFoldable}} {{MonoidConj}} (not ∘ p) xs
      ≡⟨ sym (all-foldMap (not ∘ p) xs) ⟩
        all (not ∘ p) xs
      ∎

    --
    all-not-any
      : ∀ (p : a → Bool) (xs : t a)
      → not (all p xs) ≡ any (not ∘ p) xs
    --
    all-not-any p xs =
      begin
        not (all p xs)
      ≡⟨ cong not (all-foldMap p xs) ⟩
        not (foldMap {{iFoldable}} {{MonoidConj}} p xs)
      ≡⟨ foldMap-morphism {{iFoldable}} {{isLawfulFoldable}} {{MonoidConj}} {{MonoidDisj}} deMorgan-&&-to-|| p xs ⟩
        foldMap {{iFoldable}} {{MonoidDisj}} (not ∘ p) xs
      ≡⟨ sym (any-foldMap (not ∘ p) xs) ⟩
        any (not ∘ p) xs
      ∎

{-
    all-&&
      : ∀ (xs : t a) (p q : a → Bool)
      → all (λ x → p x && q x) xs ≡ (all p xs && all q xs)
    all-&& = {!   !}
-}

    --
    all-ponens
      : ∀ (p q : a → Bool) (xs : t a)
      → all p xs ≡ True
      → all (λ x → p x ==> q x) xs ≡ True
      → all q xs ≡ True
    --
    all-ponens p q xs eq1 eq2 = trans (all-toList-universal q xs) lem3
      where
        xs' = toList xs

        lem1 : all p xs' ≡ True
        lem1 = trans (sym (all-toList-universal p xs)) eq1

        lem2 : all (λ x → p x ==> q x) xs' ≡ True
        lem2 = trans (sym (all-toList-universal (λ x → p x ==> q x) xs)) eq2

        lem3 : all q xs' ≡ True
        lem3 = all-ponens-list p q xs' lem1 lem2

{-
    any-||
      : ∀ (xs : t a) (p1 p2 : a → Bool)
      → any (λ x → p1 x || p2 x) xs ≡ (any p1 xs || any p2 xs)
    any-|| = {!   !}
-}

    --
    @0 all-elem-satisfy
      : ∀ ⦃ _ : Eq a ⦄
          ⦃ _ : IsLawfulEq a ⦄
          (p  : a → Bool)
          (xs : t a)
      → all p xs ≡ True
      → ∀ (x : a) → elem x xs ≡ True → p x ≡ True
    --
    all-elem-satisfy p xs eq1 x eq2 =
        all-elem-satisfy-list p xs' lem1 x lem2
      where
        xs' = toList xs

        lem1 : all p xs' ≡ True
        lem1 = trans (sym (all-toList-universal p xs)) eq1

        lem2 : elem x xs' ≡ True
        lem2 = trans (sym (elem-toList-universal x xs)) eq2
