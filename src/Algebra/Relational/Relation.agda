{-# OPTIONS --safe --without-K --postfix-projections #-}

module Algebra.Relational.Relation where

  open import Algebra.Relational
  open import Data.Product
  open import Data.Unit
  open import Level
  open import Relation.Binary using (REL)

  module _ {c ℓ cm cn ℓm ℓn} {R : RelSemiring c ℓ}
    (M : RelLeftSemimodule R cm ℓm)
    (N : RelLeftSemimodule R cn ℓn)
    where

    open RelSemiring R
    private
      module M = RelLeftSemimodule M
      module N = RelLeftSemimodule N

    record RelLeftSemimoduleRel (r : Level)
      : Set (c ⊔ ℓ ⊔ cm ⊔ cn ⊔ ℓm ⊔ ℓn ⊔ suc r)
      where
      field
        rel : REL M.Carrierₘ N.Carrierₘ r
      private _∼_ = rel
      field
        rel-0ₘ : ∀ {z} → M._≤0ₘ ◇ _∼ z → z N.≤0ₘ
        rel-+ₘ : ∀ {x y z} → M._≤[ x +ₘ y ] ◇ _∼ z → x ∼_ ↘ z N.≤[_+ₘ_] ↙ y ∼_
        rel-*ₘ : ∀ {r x z} → M._≤[ r *ₘ x ] ◇ _∼ z → z N.≤[ r *ₘ_] ◇ x ∼_
