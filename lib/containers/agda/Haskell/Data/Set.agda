{-# OPTIONS --erasure #-}

module Haskell.Data.Set
    {-
    ; ℙ
      ; member
      ; empty
      ; ...
    ; Prop
      ; Prop.member-empty
      ; ...
    -}
    where

open import Haskell.Prelude
  hiding (null; map; toList; filter)

{-----------------------------------------------------------------------------
    Data.Set
    Operations
------------------------------------------------------------------------------}
postulate
  ℙ : (a : Set) {{_ : Ord a}} → Set

module Operations {a : Set} {{_ : Ord a}} where
  postulate
    member : a → ℙ a → Bool

    empty  : ℙ a
    null   : ℙ a → Bool
    size   : ℙ a → Int

    insert : a → ℙ a → ℙ a
    delete : a → ℙ a → ℙ a

    union        : ℙ a → ℙ a → ℙ a
    difference   : ℙ a → ℙ a → ℙ a
    intersection : ℙ a → ℙ a → ℙ a

    filter : (a → Bool) → ℙ a → ℙ a
    map : ∀ {b : Set} {{_ : Ord b}} → (a → b) → ℙ a → ℙ b

    toAscList : ℙ a → List a
  
  singleton : a → ℙ a
  singleton x = insert x empty

  toList : ℙ a → List a
  toList = toAscList

open Operations public

{-----------------------------------------------------------------------------
    Helper lemmas
------------------------------------------------------------------------------}
--
lemma-if-b-then-True-else-False
  : ∀ (b : Bool)
  → (if b then True else False) ≡ b
--
lemma-if-b-then-True-else-False True = refl
lemma-if-b-then-True-else-False False = refl

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}
module Prop {a : Set} {{iOrd-a : Ord a}} where
  postulate
    member-empty
      : ∀ (x : a)
      → member x empty ≡ False

    member-null
      : ∀ (s : ℙ a)
      → null s ≡ True
      → ∀ (x : a) → member x s ≡ False
    
    size-null
      : ∀ (s : ℙ a)
      → null s ≡ True
      → size s ≡ 0

    size-empty
      : size {a} {{iOrd-a}} empty ≡ 0

    member-insert
      : ∀ (x xi : a) (s : ℙ a)
      → member x (insert xi s)
        ≡ (if (x == xi) then True else member x s)
    
    member-delete
      : ∀ (x xi : a) (s : ℙ a)
      → member x (delete xi s)
        ≡ (if (x == xi) then False else member x s)


    member-union
      : ∀ (x : a) (s1 s2 : ℙ a)
      → member x (union s1 s2)
        ≡ (member x s1 || member x s2)
    
    member-difference
      : ∀ (x : a) (s1 s2 : ℙ a)
      → member x (difference s1 s2)
        ≡ (member x s1 && not (member x s2))
    
    member-intersection
      : ∀ (x : a) (s1 s2 : ℙ a)
      → member x (intersection s1 s2)
        ≡ (member x s1 && member x s2)


    member-filter
      : ∀ (x : a) (p : a → Bool) (s : ℙ a)
      → member x (filter p s)
        ≡ (if p x then member x s else False)

    member-map
      : ∀ {b : Set} {{_ : Ord b}}
      → ∀ (x : a) (s : ℙ a) (f : a → b)
      → member x s ≡ member (f x) (map f s)


    elem-toAscList
      : ∀ (x : a) (s : ℙ a)
      → elem x (toAscList s) ≡ member x s

    length-toAscList
      : ∀ (s : ℙ a)
      → length (toAscList s) ≡ size s

  --
  member-singleton
    : ∀ (x xi : a)
    → member x (singleton xi) ≡ (x == xi)
  --
  member-singleton x xi =
    begin
      member x (insert xi empty)
    ≡⟨ member-insert x xi _ ⟩
      (if (x == xi) then True else member x empty)
    ≡⟨ cong (λ y → if (x == xi) then True else y) (member-empty x) ⟩
      (if (x == xi) then True else False)
    ≡⟨ lemma-if-b-then-True-else-False _ ⟩
      (x == xi)
    ∎

  