{-# OPTIONS --safe --without-K #-}

open import Algebra.Skew
open import Function.Base using (flip; _∘_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel; IsPreorder; Reflexive; Transitive)

module Generic.Linear.Thinning.Properties
  (Ty : Set) (skewSemiring : SkewSemiring 0ℓ 0ℓ)
  where

  open SkewSemiring skewSemiring
    renaming (Carrier to Ann; _≤_ to _⊴_; refl to ⊴-refl; trans to ⊴-trans)

  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.LTree.Matrix.Properties

  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Algebra skewSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Environment Ty rawSkewSemiring
  open import Generic.Linear.Thinning Ty rawSkewSemiring

  open _─Env

  private
    variable
      PΓ QΔ RΘ : Ctx
      T : Ctx → Set
      𝓥 : Scoped
      s t u : LTree
      P P′ Q Q′ R : Vector Ann s
      A : Ty

  LVar-psh : IsPresheaf LVar
  idx (LVar-psh QP lv) = idx lv
  tyq (LVar-psh QP lv) = tyq lv
  basis (LVar-psh QP lv) = ⊴*-trans QP (basis lv)

  -- The rows of a thinning's matrix are a selection of standard basis vectors
  -- (i.e, rows from the identity matrix).
  -- Which rows, exactly, is defined by the action of the thinning (lookup).
  thinning-sub-1ᴹ :
    ∀ {PΓ QΔ A}
    (th : Thinning PΓ QΔ) (v : Var A (Ctx.Γ PΓ)) →
    M th (v .idx) ⊴* 1ᴹ (th .lookup v .idx)
  thinning-sub-1ᴹ {ctx {[-]} P Γ} {ctx {t} Q Δ} th v@(var here q) =
    th .lookup v .basis
  thinning-sub-1ᴹ {PΓ} th (var (↙ i) q) =
    thinning-sub-1ᴹ
      {leftᶜ (ctx→sctx PΓ)}
      record { M = topᴹ (th .M); sums = ⊴*-refl; lookup = th .lookup ∘ leftᵛ }
      (var i q)
  thinning-sub-1ᴹ {PΓ} th (var (↘ i) q) =
    thinning-sub-1ᴹ
      {rightᶜ (ctx→sctx PΓ)}
      record { M = botᴹ (th .M); sums = ⊴*-refl; lookup = th .lookup ∘ rightᵛ }
      (var i q)

  identity : Thinning PΓ PΓ
  M identity = 1ᴹ
  sums (identity {PΓ}) .get j = *ᴹ-1ᴹ (row (Ctx.R PΓ)) .get here j
  idx (lookup identity v) = idx v
  tyq (lookup identity v) = tyq v
  basis (lookup identity v) = ⊴*-refl

  select : ∀ {PΓ QΔ RΘ : Ctx} → let ctx R Θ = RΘ in
           (∀ {A P Q} → Q ⊴* P → 𝓥 A (ctx P Θ) → 𝓥 A (ctx Q Θ)) →
           Thinning PΓ QΔ → (QΔ ─Env) 𝓥 RΘ → (PΓ ─Env) 𝓥 RΘ
  M (select 𝓥-psh th ρ) = M th *ᴹ M ρ
  sums (select {PΓ = PΓ} {QΔ} 𝓥-psh th ρ) =
    ⊴*-trans (sums ρ)
             (unrow-cong₂ (⊴ᴹ-trans (*ᴹ-mono (row-cong₂ (sums th)) ⊴ᴹ-refl)
                                    (*ᴹ-*ᴹ-→ (row (Ctx.R PΓ)) (M th) (M ρ))))
  lookup (select 𝓥-psh th ρ) v =
    𝓥-psh (⊴*-trans (unrow-cong₂ (*ᴹ-mono
                                    (row-cong₂ (thinning-sub-1ᴹ th v))
                                    ⊴ᴹ-refl))
                    (mk λ j → 1ᴹ-*ᴹ (M ρ) .get (th .lookup v .idx) j))
          (lookup ρ (plain-var (lookup th v)))

  extend : ∀ {QΔ} → Ctx.R QΔ ⊴* 0* → Thinning PΓ (PΓ ++ᶜ QΔ)
  M (extend les) i (↙ j) = 1ᴹ i j
  M (extend les) i (↘ j) = 0#
  sums (extend les) .get (↙ j) = *ᴹ-1ᴹ (row _) .get here j
  sums (extend {PΓ} {QΔ} les) .get (↘ j) =
    ⊴-trans (les .get j) (*ᴹ-0ᴹ (row (Ctx.R PΓ)) .get here j)
  idx (lookup (extend les) v) = ↙ (idx v)
  tyq (lookup (extend les) v) = tyq v
  basis (lookup (extend les) v) .get (↙ j) = ⊴-refl
  basis (lookup (extend les) v) .get (↘ j) = ⊴-refl

  -- reuse : (ren : Thinning PΓ QΔ) → P′ ⊴* unrow (row Q′ *ᴹ ren .M) →
  --         Thinning (record PΓ { R = P′ }) (record QΔ { R = Q′ })
  -- reuse ren

  extract : ∀[ □ T ⇒ T ]
  extract t = t identity

  duplicate : ∀[ □ T ⇒ □ (□ T) ]
  duplicate t ρ σ = t (select LVar-psh ρ σ)

  th^□ : Thinnable (□ T)
  th^□ = duplicate
