{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Po
open import Level using (Level; 0ℓ)

module Generic.Linear.Environment.Properties
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring
    renaming (Carrier to Ann; _≤_ to _⊴_; refl to ⊴-refl; trans to ⊴-trans)

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.Product
  open import Relation.Unary using (IUniversal)
  open import Relation.Unary.Checked
  open import Relation.Unary.Bunched.Checked
  open import Relation.Binary.PropositionalEquality

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Ty Ann hiding ([_]ᶜ)
  open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Environment Ty rawPoSemiring
  open _─Env
  open import Generic.Linear.Thinning Ty rawPoSemiring

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
  th^Env th^𝓥 {QΔ} ρ {RΘ} ren .lookup {P′ = P′} v =
    th^𝓥 (ρ .lookup v) record
      { _─Env ren
      ; sums = unrowL₂
        (⊴ᴹ-reflexive (≈ᴹ-sym (*ᴹ-assoc (row P′) (ρ .M) (ren .M))))
      }

  module With-psh^𝓥 {ℓ} {𝓥 : Scoped ℓ} (psh^𝓥 : IsPresheaf 𝓥) where

    []ᵉ : ∀[ ℑᶜ ⇒ ([]ᶜ ─Env) 𝓥 ]
    []ᵉ ℑ⟨ sp ⟩ .M = [─]
    []ᵉ ℑ⟨ sp ⟩ .sums = sp
    []ᵉ ℑ⟨ sp ⟩ .lookup (lvar (there () _) _ _)

    ++ᵉ : ∀[ (PΓ ─Env) 𝓥 ✴ᶜ (QΔ ─Env) 𝓥 ⇒ ((PΓ ++ᶜ QΔ) ─Env) 𝓥 ]
    ++ᵉ (ρ ✴⟨ sp ⟩ σ) .M = [ ρ .M
                               ─
                             σ .M ]
    ++ᵉ (ρ ✴⟨ sp ⟩ σ) .sums = ⊴*-trans sp (+*-mono (ρ .sums) (σ .sums))
    ++ᵉ (ρ ✴⟨ sp ⟩ σ) .lookup (lvar (↙ i) q b) =
      let bl , br = un++₂ b in
      psh^𝓥
        (unrowL₂ (⊴ᴹ-trans
          (+ᴹ-mono
            ⊴ᴹ-refl
            (⊴ᴹ-trans (*ᴹ-mono (rowL₂ br) ⊴ᴹ-refl) (0ᴹ-*ᴹ (σ .M))))
          (mk λ i k → +.identity-← .proj₂ _)))
        (ρ .lookup (lvar i q bl))
    ++ᵉ (ρ ✴⟨ sp ⟩ σ) .lookup (lvar (↘ i) q b) =
      let bl , br = un++₂ b in
      psh^𝓥
        (unrowL₂ (⊴ᴹ-trans
          (+ᴹ-mono
            (⊴ᴹ-trans (*ᴹ-mono (rowL₂ bl) ⊴ᴹ-refl) (0ᴹ-*ᴹ (ρ .M)))
            ⊴ᴹ-refl)
          (mk λ i k → +.identity-→ .proj₁ _)))
        (σ .lookup (lvar i q br))

    [-]ᵉ : ∀[ r ·ᶜ 𝓥 A ⇒ ([ r · A ]ᶜ ─Env) 𝓥 ]
    [-]ᵉ (⟨ sp ⟩· v) .M = row _
    [-]ᵉ (⟨ sp ⟩· v) .sums = sp
    [-]ᵉ (⟨_⟩·_ {z = P} sp v) .lookup (lvar here refl b) =
      psh^𝓥
        (unrowL₂ (⊴ᴹ-trans
          (*ᴹ-mono (rowL₂ b) (⊴ᴹ-refl {x = row P}))
          (mk λ _ _ → *.identity .proj₁ _)))
        v
