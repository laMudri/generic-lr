{-# OPTIONS --safe --without-K #-}

open import Algebra.Po
open import Level
open import Relation.Binary using (Rel)

module Generic.Linear.Thinning
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring renaming (Carrier to Ann; _≤_ to _⊴_)

  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Environment Ty poSemiring

  private
    variable
      ℓ : Level

  Thinning : (PΓ QΔ : Ctx) → Set₁
  Thinning PΓ QΔ = (PΓ ─Env) LVar QΔ

  □ : (Ctx → Set ℓ) → (Ctx → Set (suc 0ℓ ⊔ ℓ))
  (□ T) PΓ = ∀[ Thinning PΓ ⇒ T ]

  Thinnable : (Ctx → Set ℓ) → Set (suc 0ℓ ⊔ ℓ)
  Thinnable T = ∀[ T ⇒ □ T ]
