{-# OPTIONS --safe --without-K --prop --postfix-projections #-}

-- The monoidal structure of the category of thinnings

open import Algebra.Po
open import Level using (Level; 0ℓ)

module Generic.Linear.Renaming.Monoidal
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring renaming (Carrier to Ann)

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

  open With-psh^𝓥 {_𝓥_ = _∋_} psh^∋

  []ʳ : []ᶜ ⇒ʳ []ᶜ
  []ʳ = identity

  _++ʳ_ : ∀ {Γl Γr Δl Δr} →
    Γl ⇒ʳ Δl → Γr ⇒ʳ Δr → Γl ++ᶜ Γr ⇒ʳ Δl ++ᶜ Δr
  th ++ʳ ph = ++ᵉ
    (compose th ↙ʳ
      ✴⟨ +*-identity↘ _ ++ₙ +*-identity↙ _ ⟩
     compose ph ↘ʳ)

  ++-[]ʳ← : ∀ {Γ} → Γ ⇒ʳ Γ ++ᶜ []ᶜ
  ++-[]ʳ← = ++ᵉ (identity ✴⟨ +*-identity↘ _ ⟩ ([]ᵉ ℑ⟨ 0*-triv ⟩))

  ++-[]ʳ→ : ∀ {Γ} → Γ ++ᶜ []ᶜ ⇒ʳ Γ
  ++-[]ʳ→ .Ψ = [ 1ᴹ │ [│] ]
  ++-[]ʳ→ .asLinRel = [ idAsLinRel │ [│]AsLinRel ]AsLinRel
  ++-[]ʳ→ .sums = ≤*-refl , _
  ++-[]ʳ→ .lookup (le , _) (lvar i q b) = lvar (↙ i) q (≤*-trans le b ++ₙ []ₙ)
