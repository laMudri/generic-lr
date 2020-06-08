-- Algebra.Definitions, but stated carefully for left-skew structures

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Algebra.Skew.Definitions {a ℓ} {A : Set a} (_≤_ : Rel A ℓ) where

  open import Algebra.Core
  open import Data.Product

  open import Algebra.Definitions _≤_ public
    renaming (Congruent₁ to Monotonic₁; Congruent₂ to Monotonic₂)
    using (Commutative; Interchangable)
  -- With commutativity, skewness does not matter.

  LeftIdentity : A → Op₂ A → Set _
  LeftIdentity ε _∙_ = ∀ x → (ε ∙ x) ≤ x

  RightIdentity : A → Op₂ A → Set _
  RightIdentity ε _∙_ = ∀ x → x ≤ (x ∙ ε)

  Identity : A → Op₂ A → Set _
  Identity ε ∙ = (LeftIdentity ε ∙) × (RightIdentity ε ∙)

  Associative : Op₂ A → Set _
  Associative _∙_ = ∀ x y z → ((x ∙ y) ∙ z) ≤ (x ∙ (y ∙ z))

  --

  LeftAnnihilates : A → Op₂ A → Set _
  LeftAnnihilates 0# _*_ = ∀ x → (0# * x) ≤ 0#

  RightAnnihilates : A → Op₂ A → Set _
  RightAnnihilates 0# _*_ = ∀ x → 0# ≤ (x * 0#)

  Annihilates : A → Op₂ A → Set _
  Annihilates 0# * = (LeftAnnihilates 0# *) × (RightAnnihilates 0# *)

  LeftDistributes : Op₂ A → Op₂ A → Set _
  LeftDistributes _+_ _*_ = ∀ x y z → ((x + y) * z) ≤ ((x * z) + (y * z))

  RightDistributes : Op₂ A → Op₂ A → Set _
  RightDistributes _+_ _*_ = ∀ x y z → ((x * y) + (x * z)) ≤ (x * (y + z))

  Distributes : Op₂ A → Op₂ A → Set _
  Distributes + * = (LeftDistributes + *) × (RightDistributes + *)
