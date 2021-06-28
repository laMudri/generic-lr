{-# OPTIONS --safe --without-K --prop #-}

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

  infix 4 _⇒ʳ_

  private
    variable
      ℓ : Level

  _⇒ʳ_ : (PΓ QΔ : Ctx) → Set₁
  _⇒ʳ_ = [ LVar ]_⇒ᵉ_

  □ʳ : (Ctx → Set ℓ) → (Ctx → Set (suc 0ℓ ⊔ ℓ))
  (□ʳ T) PΓ = ∀[ (_⇒ʳ PΓ) ⇒ T ]

  Renameable : (Ctx → Set ℓ) → Set (suc 0ℓ ⊔ ℓ)
  Renameable T = ∀[ T ⇒ □ʳ T ]
