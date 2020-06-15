{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Algebra.Skew.Definitions.Both
  {a b m ℓ} (A : Set a) (B : Set b) {M : Set m} (_≤_ : Rel M ℓ)
  where

  open import Algebra.Core
  open import Data.Product

  Associative : Opₗ A M → Opᵣ B M → Set _
  Associative _*ₘ_ _ₘ*_ = ∀ x y z → ((x *ₘ y) ₘ* z) ≤ (x *ₘ (y ₘ* z))
