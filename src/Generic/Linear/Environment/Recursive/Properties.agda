{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ)

module Generic.Linear.Environment.Recursive.Properties
  (Ty : Set) (skewSemiring : SkewSemiring 0ℓ 0ℓ)
  where

  open SkewSemiring skewSemiring
    renaming (Carrier to Ann; _≤_ to _⊴_; refl to ⊴-refl; trans to ⊴-trans)

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.Product
  open import Function.Base using (_∘_)

  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Algebra skewSemiring
  open import Generic.Linear.Syntax Ty Ann hiding ([_]ᶜ)
  open import Generic.Linear.Syntax.Interpretation Ty rawSkewSemiring
  open import Generic.Linear.Environment.Recursive Ty rawSkewSemiring
  open import Generic.Linear.Thinning.Recursive Ty rawSkewSemiring

  open import Relation.Unary.Bunched hiding (✴1⟨_⟩; _✴⟨_⟩_; ⟨_⟩·_; lam✴; app✴)
  private
    open module Dummy0 {s} = BunchedUnit (_⊴* 0* {s})
    open module Dummy+ {s} =
      BunchedConjunction (λ (R P Q : Vector _ s) → R ⊴* P +* Q)
    open module Dummy* {s} =
      BunchedScaling (λ (R : Vector _ s) r P → R ⊴* r *ₗ P)

  private
    variable
      PΓ QΔ RΘ : Ctx
      T U : Ctx → Set
      𝓥 𝓦 : Scoped
      s t u : LTree
      Γ Δ : Vector Ty _
      P Q R : Vector Ann _
      A : Ty
      r : Ann

  {-# TERMINATING #-}  -- Structural on `s`, where `ctx {s} P Γ = PΓ`.
  Env-pres-✴1 : (PΓ ─Envᵣ) 𝓥 QΔ → ✴1ᶜ PΓ → ✴1ᶜ QΔ
  Env-pres-✴1 {PΓ = ctx {[-]} P Γ} (⟨ sp* ⟩· _) ✴1⟨ sp0 ⟩ =
    ✴1⟨ ⊴*-trans sp* (mk λ i → ⊴-trans (*-mono (sp0 .get here) ⊴-refl)
                                       (annihil .proj₁ _)) ⟩
  Env-pres-✴1 {PΓ = ctx {ε} P Γ} ρ _ = ρ
  Env-pres-✴1 {PΓ = ctx {sl <+> sr} P Γ} (ρ ✴⟨ sp+ ⟩ σ) ✴1⟨ sp0 ⟩ =
    let ✴1⟨ sp0l ⟩ = Env-pres-✴1 ρ ✴1⟨ mk (sp0 .get ∘ ↙) ⟩ in
    let ✴1⟨ sp0r ⟩ = Env-pres-✴1 σ ✴1⟨ mk (sp0 .get ∘ ↘) ⟩ in
    ✴1⟨ ⊴*-trans sp+ (⊴*-trans (+*-mono sp0l sp0r) (mk λ i → +.identity-→ .proj₁ 0#)) ⟩

  Env-pres-✴ : (PΓ ─Envᵣ) 𝓥 QΔ → (T ✴ᶜ U) PΓ → (T ✴ᶜ U) QΔ
  Env-pres-✴ {PΓ = ctx {[-]} P Γ} ρ sp = {!!}
  Env-pres-✴ {PΓ = ctx {ε} P Γ} ✴1⟨ sp0 ⟩ (t ✴⟨ sp+ ⟩ u) =
    {!Env-pres-✴ ? t!} ✴⟨ ⊴*-trans sp0 {!!} ⟩ {!!}
  Env-pres-✴ {PΓ = ctx {sl <+> sr} P Γ} ρ sp = {!!}

  th^Envᵣ : (∀ {A} → Thinnableᵣ (𝓥 A)) → Thinnableᵣ ((PΓ ─Envᵣ) 𝓥)
  th^Envᵣ {PΓ = ctx {[-]} P Γ} th^𝓥 ρ th = {!ρ!}
  th^Envᵣ {PΓ = ctx {ε} P Γ} th^𝓥 ρ th = Env-pres-✴1 th ρ
  th^Envᵣ {PΓ = ctx {s <+> t} P Γ} th^𝓥 ρ th = {!!}
