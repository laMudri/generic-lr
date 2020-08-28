{-# OPTIONS --safe --without-K --postfix-projections #-}

module Algebra.Skew.Relation where

  open import Algebra.Skew
  open import Data.Product
  open import Data.Unit
  open import Level
  open import Relation.Binary using (REL; _⇒_)

  -- NOTE: not actually used, at least for syntax `map`s.
  record ProsetRel {p pℓ q qℓ} (P : Proset p pℓ) (Q : Proset q qℓ) r
                   : Set (p ⊔ pℓ ⊔ q ⊔ qℓ ⊔ suc r) where
    private
      module P = Proset P
      module Q = Proset Q
    field
      rel : REL P.Carrier Q.Carrier r
      -- TODO: not sure about this:
      rel-mono : ∀ {px py qx qy} → rel px qx → rel py qy → px P.≤ py → qx Q.≤ qy

  module _ {c ℓ cm cn ℓm ℓn} {R : SkewSemiring c ℓ}
           (M : SkewLeftSemimodule R cm ℓm)
           (N : SkewLeftSemimodule R cn ℓn)
    where

    open SkewSemiring R
    private
      module M = SkewLeftSemimodule M
      module N = SkewLeftSemimodule N

    -- TODO: all of these could be less indexed and subsume things from
    -- Generic.Linear.Syntax.Interpretation.

    record 0ThenRel {r} (rel : REL M.Carrierₘ N.Carrierₘ r)
      (_ : ⊤) (z : N.Carrierₘ)
      : Set (r ⊔ cm ⊔ ℓm) where
      constructor _,_
      field
        {0′} : _
        sp0 : 0′ M.≤ₘ M.0ₘ
        is-rel : rel 0′ z

    record +ThenRel {r} (rel : REL M.Carrierₘ N.Carrierₘ r)
      (xy : M.Carrierₘ × M.Carrierₘ) (z : N.Carrierₘ)
      : Set (r ⊔ cm ⊔ ℓm) where
      constructor _,_
      private
        x = proj₁ xy; y = proj₂ xy
      field
        {x+y} : _
        sp+ : x+y M.≤ₘ x M.+ₘ y
        is-rel : rel x+y z

    record RelThen+ {r} (rel : REL M.Carrierₘ N.Carrierₘ r)
      (xy : M.Carrierₘ × M.Carrierₘ) (z : N.Carrierₘ)
      : Set (r ⊔ cn ⊔ ℓn) where
      constructor ⟨_,_⟩_
      private
        x = proj₁ xy; y = proj₂ xy
      field
        {x′ y′} : _
        l-rel : rel x x′
        r-rel : rel y y′
        sp+ : z N.≤ₘ x′ N.+ₘ y′

    record *ThenRel {r} (rel : REL M.Carrierₘ N.Carrierₘ r)
      (sx : Carrier × M.Carrierₘ) (z : N.Carrierₘ)
      : Set (r ⊔ cm ⊔ ℓm) where
      constructor _,_
      private
        s = proj₁ sx; x = proj₂ sx
      field
        {s*x} : _
        sp* : s*x M.≤ₘ s M.*ₘ x
        is-rel : rel s*x z

    record RelThen* {r} (rel : REL M.Carrierₘ N.Carrierₘ r)
      (sx : Carrier × M.Carrierₘ) (z : N.Carrierₘ)
      : Set (r ⊔ cn ⊔ ℓn) where
      constructor _,_
      private
        s = proj₁ sx; x = proj₂ sx
      field
        {y} : _
        is-rel : rel x y
        sp+ : z N.≤ₘ s N.*ₘ y

    record SkewLeftSemimoduleRel (r : Level)
      : Set (c ⊔ cm ⊔ cn ⊔ ℓm ⊔ ℓn ⊔ suc r)
      where
      field
        rel : REL M.Carrierₘ N.Carrierₘ r
        rel-0ₘ : 0ThenRel rel ⇒ λ _ z → z N.≤ₘ N.0ₘ
        rel-+ₘ : +ThenRel rel ⇒ RelThen+ rel
        rel-*ₘ : *ThenRel rel ⇒ RelThen* rel
