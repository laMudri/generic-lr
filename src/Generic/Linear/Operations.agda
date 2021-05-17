{-# OPTIONS --safe --without-K #-}

open import Algebra.Po
open import Relation.Binary using (Rel)
open import Level using (0ℓ)

module Generic.Linear.Operations (rawPoSemiring : RawPoSemiring 0ℓ 0ℓ 0ℓ) where

  open RawPoSemiring rawPoSemiring renaming (Carrier to Ann; _≤_ to _⊴_)

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix

  infix 4 _≈*_ _⊴*_
  infixr 6 _+*_
  infixr 8 _*ₗ_

  _≈*_ = Lift₂ _≈_
  _⊴*_ = Lift₂ _⊴_
  0* = lift₀ 0#
  _+*_ = lift₂ _+_

  _*ₗ_ : Ann → ∀ {s} → Vector Ann s → Vector Ann s
  ρ *ₗ R = lift₁ (ρ *_) R

  infix 4 _≈ᴹ_ _⊴ᴹ_
  _≈ᴹ_ = Lift₂ᴹ _≈_
  _⊴ᴹ_ = Lift₂ᴹ _⊴_

  open Zero 0# public
  open Plus _+_ public
  open Ident 0# 1# public
  open Mult 0# _+_ _*_ public
