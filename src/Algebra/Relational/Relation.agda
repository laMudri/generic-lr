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
        rel-≤ₘ : ∀ {x x′ y y′} → x M.≤ₘ x′ → y′ N.≤ₘ y → x ∼ y → x′ ∼ y′
        rel-0ₘ : ∀ {z} → M._≤0ₘ ◇ _∼ z → z N.≤0ₘ
        rel-+ₘ : ∀ {x y z} → M._≤[ x +ₘ y ] ◇ _∼ z → x ∼_ ↘ z N.≤[_+ₘ_] ↙ y ∼_
        rel-*ₘ : ∀ {r x z} → M._≤[ r *ₘ x ] ◇ _∼ z → x ∼_ ◇ z N.≤[ r *ₘ_]

    record RelLeftSemimoduleFuncRel (r : Level)
      : Set (c ⊔ ℓ ⊔ cm ⊔ cn ⊔ ℓm ⊔ ℓn ⊔ suc r)
      where
      field
        rel : REL M.Carrierₘ N.Carrierₘ r
      private _∼_ = rel
      field
        rel-≤ₘ : ∀ {x x′ y y′} → x M.≤ₘ x′ → y′ N.≤ₘ y → x ∼ y → x′ ∼ y′
        rel-0ₘ : ∀ {z} → M._≤0ₘ ◇ _∼ z → z N.≤0ₘ
        rel-+ₘ : ∀ {x y z} → M._≤[ x +ₘ y ] ◇ _∼ z → x ∼_ ↘ z N.≤[_+ₘ_] ↙ y ∼_
        rel-*ₘ : ∀ {r x z} → M._≤[ r *ₘ x ] ◇ _∼ z → x ∼_ ◇ z N.≤[ r *ₘ_]
        func : ∀ x → Universally≤ N._≤ₘ_ (x ∼_)

      relLeftSemimoduleRel : RelLeftSemimoduleRel r
      relLeftSemimoduleRel = record
        { rel = rel
        ; rel-≤ₘ = rel-≤ₘ
        ; rel-0ₘ = rel-0ₘ
        ; rel-+ₘ = rel-+ₘ
        ; rel-*ₘ = rel-*ₘ
        }
