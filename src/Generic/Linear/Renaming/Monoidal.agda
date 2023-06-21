{-# OPTIONS --safe --without-K --postfix-projections #-}

-- Ρe monoidal structure of ρe category of ρinnings

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
  open import Function.Base using (_$_; _∘_)
  open import Relation.Unary.Bunched

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Environment Ty poSemiring
  open import Generic.Linear.Environment.Properties Ty poSemiring
  open import Generic.Linear.Renaming Ty poSemiring
  open import Generic.Linear.Renaming.Properties Ty poSemiring

  open With-psh^𝓥 {𝓥 = _∋_} psh^∋

  infix 50 _++ʳ′_ _++ʳ_

  []ʳ′ : ∀ {Γ Δ : SizedCtx ε} → sctx→ctx Γ ⇒ʳ sctx→ctx Δ
  []ʳ′ = []ᵉ′ ℑᶜ⟨ []ₙ ⟩

  []ʳ : []ᶜ ⇒ʳ []ᶜ
  []ʳ = []ʳ′

  _++ʳ′_ : ∀ {sΓ tΓ sΔ tΔ}
    {Γ : SizedCtx (sΓ <+> tΓ)} {Δ : SizedCtx (sΔ <+> tΔ)} →
    leftᶜ′ Γ ⇒ʳ leftᶜ′ Δ → rightᶜ′ Γ ⇒ʳ rightᶜ′ Δ → sctx→ctx Γ ⇒ʳ sctx→ctx Δ
  _++ʳ′_ {Γ = sctx P γ} {sctx Q δ} ρ σ = ++ᵉ′ $
    (↙ʳ′ 0*-triv >>ʳ ρ)
      ✴⟨ mkᶜ {P = _ ++ _} {_ ++ _} (+*-identity↘ _ ++ₙ +*-identity↙ _) ⟩
    (↘ʳ′ 0*-triv >>ʳ σ)

  _++ʳ_ : ∀ {Γl Γr Δl Δr} →
    Γl ⇒ʳ Δl → Γr ⇒ʳ Δr → Γl ++ᶜ Γr ⇒ʳ Δl ++ᶜ Δr
  ρ ++ʳ σ = ρ ++ʳ′ σ

  ++-[]ʳ← : ∀ {Γ} → Γ ⇒ʳ Γ ++ᶜ []ᶜ
  ++-[]ʳ← = ++ᵉ (identity ✴ᶜ⟨ +*-identity↘ _ ⟩ ([]ᵉ ℑᶜ⟨ 0*-triv ⟩))

  ++-[]ʳ→ : ∀ {Γ} → Γ ++ᶜ []ᶜ ⇒ʳ Γ
  ++-[]ʳ→ .Ψ = [ 1ᴿ │ [│]ᴿ ]ᴿ
  ++-[]ʳ→ .fit-here = ≤*-refl , _
  ++-[]ʳ→ .lookup (le , _) (lvar i q b) = lvar (↙ i) q (≤*-trans le b ++ₙ []ₙ)
