{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Algebra.Skew.Definitions.Left
  {a m ℓ} (A : Set a) {M : Set m} (_≤_ : Rel M ℓ)
  where

  open import Algebra.Core
  open import Algebra.Module.Core
  open import Data.Product

  Monotonic : ∀ {ℓ′} → Rel A ℓ′ → Opₗ A M → Set _
  Monotonic _≤ᴬ_ _*_ = ∀ {x x′ y y′} → x ≤ᴬ x′ → y ≤ y′ → (x * y) ≤ (x′ * y′)

  LeftIdentity : A → Opₗ A M → Set _
  LeftIdentity 1# _*_ = ∀ x → (1# * x) ≤ x

  Associative : Op₂ A → Opₗ A M → Set _
  Associative _*_ _*ₘ_ = ∀ x y z → ((x * y) *ₘ z) ≤ (x *ₘ (y *ₘ z))

  LeftAnnihilates : A → M → Opₗ A M → Set _
  LeftAnnihilates 0# 0ₘ _*_ = ∀ x → (0# * x) ≤ 0ₘ

  RightAnnihilates : M → Opₗ A M → Set _
  RightAnnihilates 0ₘ _*_ = ∀ x → 0ₘ ≤ (x * 0ₘ)

  Annihilates : A → M → Opₗ A M → Set _
  Annihilates 0# 0ₘ * = (LeftAnnihilates 0# 0ₘ *) × (RightAnnihilates 0ₘ *)

  LeftDistributes : Op₂ A → Op₂ M → Opₗ A M → Set _
  LeftDistributes _+_ _+ₘ_ _*_ = ∀ x y z → ((x + y) * z) ≤ ((x * z) +ₘ (y * z))

  RightDistributes : Op₂ M → Opₗ A M → Set _
  RightDistributes _+ₘ_ _*_ = ∀ x y z → ((x * y) +ₘ (x * z)) ≤ (x * (y +ₘ z))

  Distributes : Op₂ A → Op₂ M → Opₗ A M → Set _
  Distributes + +ₘ * = (LeftDistributes + +ₘ *) × (RightDistributes +ₘ *)
