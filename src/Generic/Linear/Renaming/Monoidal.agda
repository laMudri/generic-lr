{-# OPTIONS --safe --without-K --prop --postfix-projections #-}

-- The monoidal structure of the category of thinnings

open import Algebra.Po
open import Level using (Level; 0ℓ)

module Generic.Linear.Renaming.Monoidal
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
  open import Generic.Linear.Renaming Ty poSemiring
  open import Generic.Linear.Renaming.Properties Ty poSemiring
  open import Generic.Linear.Extend Ty poSemiring

  open With-psh^𝓥 {_𝓥_ = _∋_} psh^∋

  []ʳ : []ᶜ ⇒ʳ []ᶜ
  []ʳ = identity

  _++ʳ_ : ∀ {PΓl PΓr QΔl QΔr} →
    PΓl ⇒ʳ QΔl → PΓr ⇒ʳ QΔr → PΓl ++ᶜ PΓr ⇒ʳ QΔl ++ᶜ QΔr
  th ++ʳ ph = ++ᵉ
    (compose th extendʳ
      ✴⟨ +*-identity↘ _ ++₂ +*-identity↙ _ ⟩
     compose ph extendˡ)

  ++-[]ʳ← : ∀ {PΓ} → PΓ ⇒ʳ PΓ ++ᶜ []ᶜ
  ++-[]ʳ← = ++ᵉ (identity ✴⟨ +*-identity↘ _ ⟩ ([]ᵉ ℑ⟨ ⊴*-refl ⟩))

  ++-[]ʳ→ : ∀ {PΓ} → PΓ ++ᶜ []ᶜ ⇒ʳ PΓ
  ++-[]ʳ→ .M = [ 1ᴹ │ [│] ]
  ++-[]ʳ→ .asLinRel = [ idAsLinRel │ [│]AsLinRel ]AsLinRel
  ++-[]ʳ→ .sums = ⊴*-refl , _
  ++-[]ʳ→ .lookup (le , _) (lvar i q b) = lvar (↙ i) q (⊴*-trans le b ++₂ []₂)
