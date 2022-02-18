
{-# OPTIONS --safe --without-K #-}

open import Algebra.Po
open import Level
open import Relation.Binary using (Rel)

module Generic.Linear.Renaming
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring renaming (Carrier to Ann)

  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Environment Ty poSemiring

  infix 20 _⇒ʳ_

  private
    variable
      ℓ : Level




  _⇒ʳ_ : (Γ Δ : Ctx) → Set₁
  _⇒ʳ_ = [ _∋_ ]_⇒ᵉ_





  □ʳ : OpenType ℓ → OpenType (suc 0ℓ ⊔ ℓ)
  (□ʳ T) Γ = ∀[ (_⇒ʳ Γ) ⇒ T ]





  Renameable : OpenType ℓ → Set (suc 0ℓ ⊔ ℓ)
  Renameable T = ∀[ T ⇒ □ʳ T ]


