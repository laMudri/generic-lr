{-# OPTIONS --safe --without-K #-}

open import Algebra using (Op₂)
open import Relation.Binary using (Rel)
open import Level using (0ℓ)

module Generic.Linear.Operations
  {Ann : Set} (_⊴_ : Rel Ann 0ℓ)
  (0# : Ann) (_+_ : Op₂ Ann) (1# : Ann) (_*_ : Op₂ Ann)
  where

  open import Data.LTree
  open import Data.LTree.Vector

  infix 4 _⊴*_
  infixr 6 _+*_
  infixr 8 _*ₗ_

  _⊴*_ = Lift₂ _⊴_
  0* = lift₀ 0#
  _+*_ = lift₂ _+_

  _*ₗ_ : Ann → ∀ {s} → Vector Ann s → Vector Ann s
  ρ *ₗ R = lift₁ (ρ *_) R
