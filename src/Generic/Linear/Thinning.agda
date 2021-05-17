{-# OPTIONS --safe --without-K #-}

open import Algebra.Po
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel)

module Generic.Linear.Thinning
  (Ty : Set) (rawPoSemiring : RawPoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open RawPoSemiring rawPoSemiring renaming (Carrier to Ann; _≤_ to _⊴_)

  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Environment Ty rawPoSemiring

  private
    variable
      ℓ : Level

  Thinning : (PΓ QΔ : Ctx) → Set
  Thinning PΓ QΔ = (PΓ ─Env) LVar QΔ

  □ : (Ctx → Set ℓ) → (Ctx → Set ℓ)
  (□ T) PΓ = ∀[ Thinning PΓ ⇒ T ]

  Thinnable : (Ctx → Set ℓ) → Set ℓ
  Thinnable T = ∀[ T ⇒ □ T ]
