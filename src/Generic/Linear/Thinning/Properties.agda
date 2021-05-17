{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Po
open import Function.Base using (flip; _∘_)
open import Level using (Level; 0ℓ)
open import Relation.Binary using (Rel; IsPreorder; Reflexive; Transitive)

module Generic.Linear.Thinning.Properties
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring
    renaming (Carrier to Ann; _≤_ to _⊴_; refl to ⊴-refl; trans to ⊴-trans)

  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Environment Ty rawPoSemiring
  open import Generic.Linear.Thinning Ty rawPoSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring
  -- open import Generic.Linear.Extend Ty poSemiring

  open _─Env

  private
    variable
      PΓ QΔ RΘ : Ctx
      ℓ : Level
      T : Ctx → Set ℓ
      𝓥 : Scoped ℓ
      s t u : LTree
      P P′ Q Q′ R : Vector Ann s
      A : Ty

  -- Also, Thinnable ⇒ IsPresheaf via subuse-th
  psh^LVar : IsPresheaf LVar
  idx (psh^LVar QP lv) = idx lv
  tyq (psh^LVar QP lv) = tyq lv
  basis (psh^LVar QP lv) = ⊴*-trans QP (basis lv)

  -- Possible lemma: if we have `Thinning PΓ QΔ` and `P ≤ R`, then `Q ≤ MR`.
  th^LVar : Thinnable (LVar A)
  th^LVar v th = record
    { LVar (th .lookup v)
    ; basis = ⊴*-trans (th .sums) (th .lookup v .basis)
    }

  {-
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
  -}

  identity : Thinning PΓ PΓ
  identity .M = 1ᴹ
  identity {ctx P Γ} .sums .get j = *ᴹ-1ᴹ (row P) .get here j
  identity .lookup v = record
    { LVar v
    ; basis = ⊴*-trans (unrowL₂ (⊴ᴹ-reflexive (*ᴹ-identityʳ _))) (v .basis)
    }

  select : ∀ {PΓ QΔ RΘ : Ctx} → let ctx R Θ = RΘ in IsPresheaf 𝓥 →
           Thinning PΓ QΔ → (QΔ ─Env) 𝓥 RΘ → (PΓ ─Env) 𝓥 RΘ
  select 𝓥-psh th ρ .M = th .M *ᴹ ρ .M
  select {PΓ = ctx P Γ} {QΔ} 𝓥-psh th ρ .sums =
    ⊴*-trans
      (ρ .sums)
      (unrow-cong₂ (⊴ᴹ-trans
        (*ᴹ-mono (row-cong₂ (th .sums)) ⊴ᴹ-refl)
        (*ᴹ-*ᴹ-→ (row P) (th .M) (ρ .M))))
  select 𝓥-psh th ρ .lookup v = 𝓥-psh
    (unrowL₂ (⊴ᴹ-reflexive (≈ᴹ-sym (*ᴹ-assoc _ (th .M) (ρ .M)))))
    (ρ .lookup (th .lookup v))

  {-
  instance
    re^LVar : RightExtend LVar
    re^LVar .embedVarʳ (var i q) = lvar (↙ i) q (⊴*-refl ++₂ ⊴*-refl)

    le^LVar : LeftExtend LVar
    le^LVar .embedVarˡ (var i q) = lvar (↘ i) q (⊴*-refl ++₂ ⊴*-refl)
  -}

  subuse-th : ∀ {Γ} → Q ⊴* P → Thinning (ctx P Γ) (ctx Q Γ)
  subuse-th QP .M = 1ᴹ
  subuse-th QP .sums = ⊴*-trans QP (unrowL₂ (*ᴹ-1ᴹ (row _)))
  subuse-th QP .lookup v = record
    { LVar v
    ; basis = ⊴*-trans (unrowL₂ (⊴ᴹ-reflexive (*ᴹ-identityʳ _))) (v .basis)
    }

  extract : ∀[ □ T ⇒ T ]
  extract t = t identity

  duplicate : ∀[ □ T ⇒ □ (□ T) ]
  duplicate t ρ σ = t (select psh^LVar ρ σ)

  th^□ : Thinnable (□ T)
  th^□ = duplicate
