{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Skew
open import Function.Base using (flip; _∘_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel; IsPreorder; Reflexive; Transitive)

module Generic.Linear.Environment.Properties
  (Ty : Set) (skewSemiring : SkewSemiring 0ℓ 0ℓ)
  where

  open SkewSemiring skewSemiring
    renaming (Carrier to Ann; _≤_ to _⊴_; refl to ⊴-refl; trans to ⊴-trans)

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Vector.Properties
  open import Data.LTree.Matrix
  open import Data.LTree.Matrix.Properties
  open import Data.Product
  open import Relation.Unary
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
      T : Ctx → Set
      𝓥 𝓦 : Scoped
      s t u : LTree
      P Q R : Vector Ann s
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

  []ᵉ : ∀[ ✴1 ⇒ ([]ᶜ ─Env) 𝓥 ]
  []ᵉ ✴1⟨ sp ⟩ .M = [─]
  []ᵉ ✴1⟨ sp ⟩ .sums = sp
  []ᵉ ✴1⟨ sp ⟩ .lookup (var (there () _) _)

  ++ᵉ : ∀[ (PΓ ─Env) 𝓥 ✴ (QΔ ─Env) 𝓥 ⇒ ((PΓ ++ᶜ QΔ) ─Env) 𝓥 ]
  ++ᵉ (ρ ✴⟨ sp ⟩ σ) .M = [ ρ .M
                             ─
                           σ .M ]
  ++ᵉ (ρ ✴⟨ sp ⟩ σ) .sums = ⊴*-trans sp (+*-mono (ρ .sums) (σ .sums))
  ++ᵉ (ρ ✴⟨ sp ⟩ σ) .lookup (var (↙ i) q) = ρ .lookup (var i q)
  ++ᵉ (ρ ✴⟨ sp ⟩ σ) .lookup (var (↘ i) q) = σ .lookup (var i q)

  [-]ᵉ : ∀[ r · 𝓥 A ⇒ ([ r · A ]ᶜ ─Env) 𝓥 ]
  [-]ᵉ (⟨ sp ⟩· v) .M = row _
  [-]ᵉ (⟨ sp ⟩· v) .sums = sp
  [-]ᵉ (⟨ sp ⟩· v) .lookup (var _ refl) = v

  -- _<$>_ : ((∀ {A} → 𝓥 A record QΔ { R = N i } → 𝓦 A RΘ) ×
  --          ∃ \ N → Ctx.R RΘ ⊴* unrow (row (Ctx.R QΔ) *ᴹ N)) →
  --         (PΓ ─Env) 𝓥 QΔ → (PΓ ─Env) 𝓦 RΘ
  -- ((f , N , sp) <$> ρ) .M = ρ .M *ᴹ N
  -- ((f , N , sp) <$> ρ) .sums =
  --   ⊴*-trans sp (unrowL₂
  --   (⊴ᴹ-trans (*ᴹ-mono (rowL₂ (ρ .sums)) ⊴ᴹ-refl)
  --             (*ᴹ-*ᴹ-→ _ (ρ .M) N)))
  -- ((f , N , sp) <$> ρ) .lookup v =
  --   {!(ρ .lookup v)!}
