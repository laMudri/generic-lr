{-# OPTIONS --without-K --safe #-}

module Algebra.Skew where

  open import Algebra.Core using (Op₂)
  import Algebra.Skew.Definitions as Defs
  open import Function.Base using (flip)
  open import Level
  open import Relation.Binary.Core using (Rel; _Preserves_⟶_)
  open import Relation.Binary.Definitions

  record IsProset {c ℓ} {C : Set c} (≤ : Rel C ℓ) : Set (c ⊔ ℓ) where
    field
      refl : Reflexive ≤
      trans : Transitive ≤

  record IsSkewMonoid {c ℓ} {C : Set c} (≤ : Rel C ℓ)
                      (ε : C) (∙ : Op₂ C) : Set (c ⊔ ℓ) where
    open Defs ≤
    field
      mono : Monotonic₂ ∙
      identity : Identity ε ∙
      assoc : Associative ∙

  -- Same as IsCommutativeMonoid, except without a _≈_.
  record IsSkewCommutativeMonoid {c ℓ} {C : Set c} (≤ : Rel C ℓ)
                                 (ε : C) (∙ : Op₂ C) : Set (c ⊔ ℓ) where
    open Defs ≤
    field
      isLeftSkewMonoid : IsSkewMonoid ≤ ε ∙
      isRightSkewMonoid : IsSkewMonoid (flip ≤) ε ∙
      comm : Commutative ∙
    open IsSkewMonoid isLeftSkewMonoid public
      renaming (identity to identity-→; assoc to assoc-→)
    open IsSkewMonoid isRightSkewMonoid public
      hiding (mono)
      renaming (identity to identity-←; assoc to assoc-←)

  record IsSkewSemiring {c ℓ} {C : Set c} (≤ : Rel C ℓ)
                        (0# : C) (+ : Op₂ C) (1# : C) (* : Op₂ C)
                        : Set (c ⊔ ℓ) where
    open Defs ≤
    field
      isProset : IsProset ≤
      +-isSkewCommutativeMonoid : IsSkewCommutativeMonoid ≤ 0# +
      *-isSkewMonoid : IsSkewMonoid ≤ 1# *
      annihil : Annihilates 0# *
      distrib : Distributes + *
    open IsProset isProset public
    module + = IsSkewCommutativeMonoid +-isSkewCommutativeMonoid
    module * = IsSkewMonoid *-isSkewMonoid

  record SkewSemiring c ℓ : Set (suc (c ⊔ ℓ)) where
    infix 4 _≤_
    infix 6 _+_
    infix 7 _*_
    field
      Carrier : Set c
      _≤_ : Rel Carrier ℓ
      0# : Carrier
      _+_ : Op₂ Carrier
      1# : Carrier
      _*_ : Op₂ Carrier
      isSkewSemiring : IsSkewSemiring _≤_ 0# _+_ 1# _*_
    open IsSkewSemiring isSkewSemiring public

  --

  record SkewSemiringMor {r rℓ s sℓ} (R : SkewSemiring r rℓ)
                                     (S : SkewSemiring s sℓ)
                         : Set (r ⊔ rℓ ⊔ s ⊔ sℓ) where
    private
      module R = SkewSemiring R
      module S = SkewSemiring S
      open S using (_≤_)
    field
      apply : R.Carrier → S.Carrier
      hom-mono : apply Preserves R._≤_ ⟶ S._≤_
      hom-0# : apply R.0# ≤ S.0#
      hom-+ : ∀ x y → apply (x R.+ y) ≤ apply x S.+ apply y
      hom-1# : apply R.1# ≤ S.1#
      hom-* : ∀ x y → apply (x R.* y) ≤ apply x S.* apply y
