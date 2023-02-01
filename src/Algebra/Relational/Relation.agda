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
        rel-≤ₘ : ∀ {x x′ y y′} → x′ M.≤ₘ x → y N.≤ₘ y′ → x ∼ y → x′ ∼ y′
        rel-0ₘ : ∀ {z} → z ∼_ ◇ N._≤0ₘ → z M.≤0ₘ
        rel-+ₘ : ∀ {x y z} → z ∼_ ◇ N._≤[ x +ₘ y ] → _∼ x ↘ z M.≤[_+ₘ_] ↙ _∼ y
        rel-*ₘ : ∀ {r x z} → z ∼_ ◇ N._≤[ r *ₘ x ] → _∼ x ◇ z M.≤[ r *ₘ_]

    record RelLeftSemimoduleFuncRel (r : Level)
      : Set (c ⊔ ℓ ⊔ cm ⊔ cn ⊔ ℓm ⊔ ℓn ⊔ suc r)
      where
      field
        rel : REL M.Carrierₘ N.Carrierₘ r
      private _∼_ = rel
      field
        rel-≤ₘ : ∀ {x x′ y y′} → x′ M.≤ₘ x → y N.≤ₘ y′ → x ∼ y → x′ ∼ y′
        rel-0ₘ : ∀ {z} → z ∼_ ◇ N._≤0ₘ → z M.≤0ₘ
        rel-+ₘ : ∀ {x y z} → z ∼_ ◇ N._≤[ x +ₘ y ] → _∼ x ↘ z M.≤[_+ₘ_] ↙ _∼ y
        rel-*ₘ : ∀ {r x z} → z ∼_ ◇ N._≤[ r *ₘ x ] → _∼ x ◇ z M.≤[ r *ₘ_]
        func : ∀ y → Universally≤ M._≤ₘ_ (_∼ y)

      relLeftSemimoduleRel : RelLeftSemimoduleRel r
      relLeftSemimoduleRel = record
        { rel = rel
        ; rel-≤ₘ = rel-≤ₘ
        ; rel-0ₘ = rel-0ₘ
        ; rel-+ₘ = rel-+ₘ
        ; rel-*ₘ = rel-*ₘ
        }
