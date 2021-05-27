{-# OPTIONS --safe --without-K --prop --postfix-projections #-}

open import Algebra.Skew
open import Level using (Level; 0ℓ)

module Generic.Linear.Environment.Properties
  (Ty : Set) (skewSemiring : SkewSemiring 0ℓ 0ℓ)
  where

  open SkewSemiring skewSemiring
    renaming (Carrier to Ann; _≤_ to _⊴_; refl to ⊴-refl; trans to ⊴-trans)

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.Product
  open import Relation.Unary using (IUniversal)
  open import Relation.Unary.Checked
  open import Relation.Unary.Bunched.Checked
  open import Relation.Binary.PropositionalEquality

  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Algebra skewSemiring
  open import Generic.Linear.Syntax Ty Ann hiding ([_]ᶜ)
  open import Generic.Linear.Syntax.Interpretation Ty rawSkewSemiring
  open import Generic.Linear.Environment Ty rawSkewSemiring
  open _─Env
  open import Generic.Linear.Thinning Ty rawSkewSemiring

  private
    variable
      PΓ QΔ RΘ : Ctx
      ℓ : Level
      𝓥 : Scoped ℓ
      A : Ty
      r : Ann

  th^Env : (∀ {A} → Thinnable (𝓥 A)) → Thinnable ((PΓ ─Env) 𝓥)
  th^Env th^𝓥 ρ ren .M = ρ .M *ᴹ ren .M
  th^Env th^𝓥 ρ ren .sums =
    ⊴*-trans (ren .sums)
             (⊴*-trans (unrowL₂ (*ᴹ-mono (rowL₂ (ρ .sums)) ⊴ᴹ-refl))
                       (unrowL₂ (*ᴹ-*ᴹ-→ _ (ρ .M) (ren .M))))
  th^Env th^𝓥 {QΔ} ρ {RΘ} ren .lookup v =
    th^𝓥 (ρ .lookup v) record { _─Env ren; sums = ⊴*-refl }

  []ᵉ : ∀[ ℑᶜ ⇒ ([]ᶜ ─Env) 𝓥 ]
  []ᵉ ℑ⟨ sp ⟩ .M = [─]
  []ᵉ ℑ⟨ sp ⟩ .sums = sp
  []ᵉ ℑ⟨ sp ⟩ .lookup (var (there () _) _)

  ++ᵉ : ∀[ (PΓ ─Env) 𝓥 ✴ᶜ (QΔ ─Env) 𝓥 ⇒ ((PΓ ++ᶜ QΔ) ─Env) 𝓥 ]
  ++ᵉ (ρ ✴⟨ sp ⟩ σ) .M = [ ρ .M
                             ─
                           σ .M ]
  ++ᵉ (ρ ✴⟨ sp ⟩ σ) .sums = ⊴*-trans sp (+*-mono (ρ .sums) (σ .sums))
  ++ᵉ (ρ ✴⟨ sp ⟩ σ) .lookup (var (↙ i) q) = ρ .lookup (var i q)
  ++ᵉ (ρ ✴⟨ sp ⟩ σ) .lookup (var (↘ i) q) = σ .lookup (var i q)

  [-]ᵉ : ∀[ r ·ᶜ 𝓥 A ⇒ ([ r · A ]ᶜ ─Env) 𝓥 ]
  [-]ᵉ (⟨ sp ⟩· v) .M = row _
  [-]ᵉ (⟨ sp ⟩· v) .sums = sp
  [-]ᵉ (⟨ sp ⟩· v) .lookup (var _ refl) = v
