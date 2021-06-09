{-# OPTIONS --safe --without-K #-}

open import Algebra.Po
open import Relation.Binary using (Rel; REL)
open import Level using (0ℓ; suc)

module Generic.Linear.Operations (rawPoSemiring : RawPoSemiring 0ℓ 0ℓ 0ℓ) where

  open RawPoSemiring rawPoSemiring renaming (Carrier to Ann; _≤_ to _⊴_)

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Function.Base

  infix 4 _≈*_ _⊴*_
  infixr 6 _+*_
  infixr 8 _*ₗ_

  _≈*_ = Lift₂ _≈_
  _⊴*_ = Lift₂ _⊴_
  0* = lift₀ 0#
  _+*_ = lift₂ _+_

  _*ₗ_ : Ann → ∀ {s} → Vector Ann s → Vector Ann s
  ρ *ₗ R = lift₁ (ρ *_) R

  ⟨_∣ : ∀ {s} → Ptr s → Vector Ann s
  ⟨_∣ = 1ᴹ  where open Ident 0# 1#
