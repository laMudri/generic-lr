{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Algebra.Skew.Definitions.Right
  {a m ℓ} (A : Set a) {M : Set m} (_≤_ : Rel M ℓ)
  where

  open import Algebra.Core
  open import Data.Product

  Monotonic : ∀ {ℓ′} → Rel A ℓ′ → Opᵣ A M → Set _
  Monotonic _≤ᴬ_ _*_ = ∀ {x x′ y y′} → x ≤ x′ → y ≤ᴬ y′ → (x * y) ≤ (x′ * y′)

  RightIdentity : A → Opᵣ A M → Set _
  RightIdentity 1# _*_ = ∀ x → x ≤ (x * 1#)

  Associative : Op₂ A → Opᵣ A M → Set _
  Associative _*_ _ₘ*_ = ∀ x y z → ((x ₘ* y) ₘ* z) ≤ (x ₘ* (y * z))

  LeftAnnihilates : M → Opᵣ A M → Set _
  LeftAnnihilates 0ₘ _*_ = ∀ x → (0ₘ * x) ≤ 0ₘ

  RightAnnihilates : A → M → Opᵣ A M → Set _
  RightAnnihilates 0# 0ₘ _*_ = ∀ x → 0ₘ ≤ (x * 0#)

  Annihilates : A → M → Opᵣ A M → Set _
  Annihilates 0# 0ₘ * = (LeftAnnihilates 0ₘ *) × (RightAnnihilates 0# 0ₘ *)

  LeftDistributes : Op₂ M → Opᵣ A M → Set _
  LeftDistributes _+ₘ_ _*_ = ∀ x y z → ((x +ₘ y) * z) ≤ ((x * z) +ₘ (y * z))

  RightDistributes : Op₂ A → Op₂ M → Opᵣ A M → Set _
  RightDistributes _+_ _+ₘ_ _*_ = ∀ x y z → ((x * y) +ₘ (x * z)) ≤ (x * (y + z))

  Distributes : Op₂ A → Op₂ M → Opᵣ A M → Set _
  Distributes + +ₘ * = (LeftDistributes +ₘ *) × (RightDistributes + +ₘ *)
