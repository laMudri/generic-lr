{-# OPTIONS --safe --without-K #-}

open import Algebra.Skew
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel)

module Generic.Linear.Environment.Recursive
  (Ty : Set) (rawSkewSemiring : RawSkewSemiring 0ℓ 0ℓ)
  where

  open RawSkewSemiring rawSkewSemiring renaming (Carrier to Ann; _≤_ to _⊴_)

  open import Data.LTree
  open import Data.LTree.Vector

  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawSkewSemiring
    using (✴1ᶜ; _✴ᶜ_; _·ᶜ_)

  open import Function.Base using (_∘_)

  open import Relation.Unary.Bunched
  private
    open module Dummy0 {s} = BunchedUnit (_⊴* 0* {s})
    open module Dummy+ {s} =
      BunchedConjunction (λ (R P Q : Vector _ s) → R ⊴* P +* Q)
    open module Dummy* {s} =
      BunchedScaling (λ (R : Vector _ s) r P → R ⊴* r *ₗ P)

  module _─Envᵣ (𝓥 : Scoped) where
    go : ∀ {s} → Vector Ann s → Vector Ty s → Ctx → Set
    go {[-]} P Γ = P here ·ᶜ 𝓥 (Γ here)
    go {ε} P Γ = ✴1ᶜ
    go {s <+> t} P Γ = go (P ∘ ↙) (Γ ∘ ↙) ✴ᶜ go (P ∘ ↘) (Γ ∘ ↘)

  _─Envᵣ : (PΓ : Ctx) (𝓥 : Scoped) (QΔ : Ctx) → Set
  (ctx P Γ ─Envᵣ) 𝓥 QΔ = _─Envᵣ.go 𝓥 P Γ QΔ
