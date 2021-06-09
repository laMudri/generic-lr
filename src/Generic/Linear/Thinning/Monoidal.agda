{-# OPTIONS --safe --without-K --prop --postfix-projections #-}

-- The monoidal structure of the category of thinnings

open import Algebra.Po
open import Level using (Level; 0ℓ)

module Generic.Linear.Thinning.Monoidal
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring
    renaming (Carrier to Ann; _≤_ to _⊴_; refl to ⊴-refl; trans to ⊴-trans)

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.Product
  open import Data.Unit
  open import Relation.Unary.Bunched

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Environment Ty poSemiring
  open import Generic.Linear.Environment.Properties Ty poSemiring
  open import Generic.Linear.Thinning Ty poSemiring
  open import Generic.Linear.Thinning.Properties Ty poSemiring
  open import Generic.Linear.Extend Ty poSemiring

  open With-psh^𝓥 {𝓥 = LVar} psh^LVar

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
  ++-[]ᵗ← .asLinRel = [ idAsLinRel │ [│]AsLinRel ]AsLinRel
  ++-[]ᵗ← .sums = ⊴*-refl , _
  ++-[]ᵗ← .lookup (le , _) (lvar i q b) = lvar (↙ i) q (⊴*-trans le b ++₂ []₂)
