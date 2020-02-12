{-# OPTIONS --safe --without-K #-}

-- The shape of a binary tree

module Data.LTree where

  open import Data.Bool using (Bool; true; false)
  open import Data.Product as Σ
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable

  infix 5 _<+>_

  -- A tree is either a box (there), empty, or a pair of trees

  data LTree : Set where
    [-] : LTree
    ε : LTree
    _<+>_ : (s t : LTree) → LTree

  private
    variable
      s s′ t : LTree

  -- Pointers to boxes

  data Ptr : LTree → Set
  data In-node : (s t : LTree) → Set

  data Ptr where
    here : Ptr [-]
    there : (d : In-node s t) → Ptr s → Ptr t

  data In-node where
    left : In-node s (s <+> t)
    right : In-node t (s <+> t)

  pattern go-left s = there left s
  pattern go-right s = there right s

  private
    example-ltree : LTree
    example-ltree = ([-] <+> [-]) <+> (ε <+> [-])

    example-ptr : Ptr example-ltree
    example-ptr = go-left (go-right here)

  there-injective :
    {d : In-node s t} {e : In-node s′ t} {i : Ptr s} {j : Ptr s′} →
    there d i ≡ there e j →
    Σ[ sq ∈ s ≡ s′ ] (subst (λ z → In-node z t) sq d ≡ e × subst Ptr sq i ≡ j)
  there-injective refl = refl , refl , refl

  go-left-injective :
    {i j : Ptr s} → there (left {t = t}) i ≡ there left j → i ≡ j
  go-left-injective refl = refl

  go-right-injective :
    {i j : Ptr t} → there (right {s = s}) i ≡ there right j → i ≡ j
  go-right-injective refl = refl

  _≟_ : (i j : Ptr s) → Dec (i ≡ j)
  here ≟ here = yes refl
  go-left i ≟ go-left j = map′ (cong go-left) go-left-injective (i ≟ j)
  go-left i ≟ go-right j = no λ ()
  go-right i ≟ go-left j = no λ ()
  go-right i ≟ go-right j = map′ (cong go-right) go-right-injective (i ≟ j)

  _==_ : (i j : Ptr s) → Bool
  i == j = does (i ≟ j)
