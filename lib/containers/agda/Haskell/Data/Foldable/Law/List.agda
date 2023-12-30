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

{-----------------------------------------------------------------------------
    Various properties for List
------------------------------------------------------------------------------}
private
  bang : ∀ {A : Set} → False ≡ True → A
  bang ()

--
all-const-True-list
    : ∀ (ys : List a)
    → all (const True) ys ≡ True
--
all-const-True-list [] = refl
all-const-True-list (y ∷ ys) = all-const-True-list ys

--
all-ponens-list
    : ∀ (p q : a → Bool) (xs : List a)
    → all p xs ≡ True
    → all (λ x → p x ==> q x) xs ≡ True
    → all q xs ≡ True
--
all-ponens-list p q [] refl refl = refl
all-ponens-list p q (x ∷ xs) eq1 eq2 =
    &&-semantics (q x) _ lem3 (all-ponens-list p q xs lem1 lem2)
  where
    lem1 : _
    lem1 = &&-rightTrue (p x) _ eq1

    lem2 : _
    lem2 = &&-rightTrue (p x ==> q x) _ eq2

    lem3 : q x ≡ True
    lem3 =
        Bool.Prop.==>-ponens (p x) (q x)
        (&&-leftTrue (p x) _ eq1)
        (&&-leftTrue (p x ==> q x) _ eq2)

--
@0 all-not-any-list
  : ∀ (p : a → Bool)
      (xs : List a)
  → not (all p xs) ≡ any (not ∘ p) xs
--
all-not-any-list p xs =
  begin
    not (all p xs)
  ≡⟨ cong not (all-foldMap p xs) ⟩
    not (foldMapList {{MonoidConj}} p xs)
  ≡⟨ foldMap-morphism {{_}} {{isLawfulFoldableList}} {{MonoidConj}} {{MonoidDisj}} deMorgan-&&-to-|| p xs ⟩
    foldMapList {{MonoidDisj}} (not ∘ p) xs
  ≡⟨ sym (any-foldMap (not ∘ p) xs) ⟩
    any (not ∘ p) xs
  ∎

--
@0 any-not-all-list
  : ∀ (p : a → Bool)
      (xs : List a)
  → not (any p xs) ≡ all (not ∘ p) xs
--
any-not-all-list p xs =
  begin
    not (any p xs)
  ≡⟨ cong not (any-foldMap p xs) ⟩
    not (foldMapList {{MonoidDisj}} p xs)
  ≡⟨ foldMap-morphism {{_}} {{isLawfulFoldableList}} {{MonoidDisj}} {{MonoidConj}} deMorgan-||-to-&& p xs ⟩
    foldMapList {{MonoidConj}} (not ∘ p) xs
  ≡⟨ sym (all-foldMap (not ∘ p) xs) ⟩
    all (not ∘ p) xs
  ∎

--
@0 all-elem-satisfy-list
  : ∀ ⦃ _ : Eq a ⦄
      ⦃ _ : IsLawfulEq a ⦄
      (p  : a → Bool)
      (xs : List a)
  → all p xs ≡ True
  → ∀ (x : a) → elem x xs ≡ True → p x ≡ True
--
all-elem-satisfy-list {a} p xs eq1 x0 eq2 =
  case p x0 of λ
    { True {{eq}} → eq
    ; False {{eq}} →
      bang
        ( trans
            (sym lem2)
            (all-ponens-list p q xs eq1 (lem1 eq))
        )
    }
  where
    q : a → Bool
    q y = not (x0 == y)

    lem0 : ∀ (b : Bool) → (b || True) ≡ True
    lem0 True = refl 
    lem0 False = refl

    lem1
      : p x0 ≡ False
      → all (λ y → p y ==> q y) xs ≡ True
    lem1 eq0 =
        begin
          all (λ y → p y ==> q y) xs
        ≡⟨ cong (λ r → all r xs) (ext lem11) ⟩
          all (const True) xs
        ≡⟨ all-const-True-list xs ⟩
          True
        ∎
      where
        lem11 : ∀ (y : a) → (p y ==> q y) ≡ True
        lem11 y = case x0 == y of λ
          { True {{eq}} →
              begin
                p y ==> q y
              ≡⟨ cong (λ z → p z ==> q z) (sym (equality x0 y eq)) ⟩
                p x0 ==> q x0
              ≡⟨ cong (λ z → p x0 ==> not z) (equality' x0 x0 refl) ⟩
                p x0 ==> not True
              ≡⟨ cong (_==> False) eq0 ⟩
                False ==> False
              ∎
          ; False {{eq}} →
              begin
                p y ==> q y
              ≡⟨ cong (λ z → p y ==> not z) eq ⟩
                p y ==> True
              ≡⟨ lem0 (not (p y)) ⟩
                True
              ∎
          }  

    lem2 : all q xs ≡ False
    lem2 =
      begin
        all (not ∘ (x0 ==_)) xs
      ≡⟨ sym (any-not-all-list (x0 ==_) xs) ⟩
        not (any (x0 ==_) xs)
      ≡⟨ cong not (sym (elem-any x0 xs)) ⟩
        not (elem x0 xs)
      ≡⟨ cong not eq2 ⟩
        not True
      ∎
