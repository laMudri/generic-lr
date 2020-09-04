{-# OPTIONS --safe --without-K #-}

open import Algebra.Skew
open import Relation.Binary using (Rel)
open import Level using (0ℓ)

module Generic.Linear.Operations (rawSkewSemiring : RawSkewSemiring 0ℓ 0ℓ) where

  open RawSkewSemiring rawSkewSemiring renaming (Carrier to Ann; _≤_ to _⊴_)

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix

  infix 4 _⊴*_
  infixr 6 _+*_
  infixr 8 _*ₗ_

  _⊴*_ = Lift₂ _⊴_
  0* = lift₀ 0#
  _+*_ = lift₂ _+_

  _*ₗ_ : Ann → ∀ {s} → Vector Ann s → Vector Ann s
  ρ *ₗ R = lift₁ (ρ *_) R

  open Zero 0# public
  open Plus _+_ public
  open Ident 0# 1# public
  open Mult 0# _+_ _*_ public
