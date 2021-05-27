{-# OPTIONS --safe --without-K --prop --postfix-projections #-}

-- The monoidal structure of the category of thinnings

open import Algebra.Skew
open import Level using (Level; 0ℓ)

module Generic.Linear.Thinning.Monoidal
  (Ty : Set) (skewSemiring : SkewSemiring 0ℓ 0ℓ)
  where

  open SkewSemiring skewSemiring
    renaming (Carrier to Ann; _≤_ to _⊴_; refl to ⊴-refl; trans to ⊴-trans)

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Relation.Unary.Bunched

  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Algebra skewSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Environment Ty rawSkewSemiring
  open import Generic.Linear.Environment.Properties Ty skewSemiring
  open import Generic.Linear.Thinning Ty rawSkewSemiring
  open import Generic.Linear.Thinning.Properties Ty skewSemiring
  open import Generic.Linear.Extend Ty skewSemiring

  open _─Env

  []ᵗ : Thinning []ᶜ []ᶜ
  []ᵗ = identity

  _++ᵗ_ : ∀ {PΓl PΓr QΔl QΔr} →
    Thinning PΓl QΔl → Thinning PΓr QΔr → Thinning (PΓl ++ᶜ PΓr) (QΔl ++ᶜ QΔr)
  th ++ᵗ ph = ++ᵉ
    (compose th extendʳ
      ✴⟨ +*-identity↘ _ ++₂ +*-identity↙ _ ⟩
     compose ph extendˡ)

  ++-[]ᵗ→ : ∀ {PΓ} → Thinning (PΓ ++ᶜ []ᶜ) PΓ
  ++-[]ᵗ→ = ++ᵉ (identity ✴⟨ +*-identity↘ _ ⟩ ([]ᵉ ℑ⟨ ⊴*-refl ⟩))

  ++-[]ᵗ← : ∀ {PΓ} → Thinning PΓ (PΓ ++ᶜ []ᶜ)
  ++-[]ᵗ← .M = [ 1ᴹ │ [│] ]
  ++-[]ᵗ← .sums = unrowL₂ (*ᴹ-1ᴹ _) ++₂ []₂
  ++-[]ᵗ← .lookup (var i q) = lvar (↙ i) q (⊴*-refl ++₂ []₂)
