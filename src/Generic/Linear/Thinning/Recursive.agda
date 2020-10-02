{-# OPTIONS --safe --without-K #-}

open import Algebra.Skew
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel)

module Generic.Linear.Thinning.Recursive
  (Ty : Set) (rawSkewSemiring : RawSkewSemiring 0ℓ 0ℓ)
  where

  open RawSkewSemiring rawSkewSemiring renaming (Carrier to Ann; _≤_ to _⊴_)

  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix

  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Environment.Recursive Ty rawSkewSemiring

  open import Generic.Linear.Thinning Ty rawSkewSemiring public
    using (LVar; lvar; idx; tyq; basis; plain-var)

  Thinningᵣ : (PΓ QΔ : Ctx) → Set
  Thinningᵣ PΓ QΔ = (PΓ ─Envᵣ) LVar QΔ

  □ᵣ : (Ctx → Set) → (Ctx → Set)
  (□ᵣ T) PΓ = ∀[ Thinningᵣ PΓ ⇒ T ]

  Thinnableᵣ : (Ctx → Set) → Set
  Thinnableᵣ T = ∀[ T ⇒ □ᵣ T ]
