{-# OPTIONS --safe --sized-types --without-K --postfix-projections #-}

open import Algebra.Po
open import Level using (Level; 0ℓ; _⊔_; suc)

module Generic.Linear.Semantics
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring
    renaming (Carrier to Ann
             ; _≤_ to _⊴_
             ; refl to ⊴-refl; trans to ⊴-trans
             )

  open import Algebra.Po.Relation
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.Product
  open import Function using (Equivalence)
  open import Size
  open import Relation.Unary
  open import Relation.Unary.Bunched

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring
  open import Generic.Linear.Syntax.Interpretation.Map Ty poSemiring
  open import Generic.Linear.Syntax.Term Ty rawPoSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Environment Ty poSemiring
  open import Generic.Linear.Thinning Ty poSemiring
  open import Generic.Linear.Thinning.Properties Ty poSemiring
  open import Generic.Linear.Environment.Properties Ty poSemiring

  private
    variable
      A : Ty
      ℓ v c : Level
      fl : PremisesFlags

  Kripke : (𝓥 : Scoped v) (𝓒 : Scoped c) (PΓ : Ctx) (A : Ty) →
           Ctx → Set _
  Kripke 𝓥 𝓒 PΓ A = □ ((PΓ ─Env) 𝓥 ─✴ᶜ 𝓒 A)

  mapK𝓒 : ∀ {v c c′} {𝓥 : Scoped v} {𝓒 : Scoped c} {𝓒′ : Scoped c′} →
          (∀ {A} → ∀[ 𝓒 A ⇒ 𝓒′ A ]) →
          ∀ {PΓ A} → ∀[ Kripke 𝓥 𝓒 PΓ A ⇒ Kripke 𝓥 𝓒′ PΓ A ]
  mapK𝓒 f b th .app✴ sp ρ = f (b th .app✴ sp ρ)

  record Semantics (d : System fl) (𝓥 : Scoped v) (𝓒 : Scoped c)
                   : Set (suc 0ℓ ⊔ v ⊔ c) where
    field
      th^𝓥 : Thinnable (𝓥 A)
      var : ∀[ 𝓥 A ⇒ 𝓒 A ]
      alg : ∀[ ⟦ d ⟧s (Kripke 𝓥 𝓒) A ⇒ 𝓒 A ]

    psh^𝓥 : IsPresheaf 𝓥
    psh^𝓥 QP v = th^𝓥 v (subuse-th QP)
    open With-psh^𝓥 psh^𝓥

    _─Comp : Ctx → Scoped ℓ → Ctx → Set ℓ
    (PΓ ─Comp) 𝓒 QΔ = ∀ {sz A} → Tm d sz A PΓ → 𝓒 A QΔ

    semantics : ∀ {PΓ QΔ} → (PΓ ─Env) 𝓥 QΔ → (PΓ ─Comp) 𝓒 QΔ
    body : ∀ {PΓ QΔ sz} → (PΓ ─Env) 𝓥 QΔ → ∀ {RΘ A} →
           Scope (Tm d sz) RΘ A PΓ → Kripke 𝓥 𝓒 RΘ A QΔ

    semantics ρ (`var v) = var (ρ .lookup (ρ .sums) v)
    semantics {ctx P Γ} {ctx Q Δ} ρ (`con {sz = sz} t) =
      alg (map-s (ρ .M) d
        (λ r → body (record { _─Env ρ; sums = ρ .asLinRel .equiv .g r }))
        (sums-⊴* ρ) t)
      where open Equivalence

    body ρ t th .app✴ r σ =
      let ρ′ = th^Env th^𝓥 ρ th in
      semantics (++ᵉ (ρ′ ✴⟨ r ⟩ σ)) t
