{-# OPTIONS --safe --sized-types --without-K #-}

open import Algebra.Skew
open import Level using (0ℓ)

module Generic.Linear.Semantics
  (Ty : Set) (skewSemiring : SkewSemiring 0ℓ 0ℓ)
  where

  open SkewSemiring skewSemiring
    renaming (Carrier to Ann
             ; _≤_ to _⊴_
             ; refl to ⊴-refl; trans to ⊴-trans
             )

  open import Algebra.Skew.Relation
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.Product
  open import Size
  open import Relation.Unary

  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Algebra skewSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawSkewSemiring
  open import Generic.Linear.Syntax.Interpretation.Map Ty skewSemiring
  open import Generic.Linear.Syntax.Term Ty rawSkewSemiring
  open import Generic.Linear.Environment Ty rawSkewSemiring hiding (var)
  open import Generic.Linear.Thinning Ty rawSkewSemiring
  open _─Env
  open import Generic.Linear.Thinning.Properties Ty skewSemiring
  open import Generic.Linear.Environment.Properties Ty skewSemiring

  private
    variable
      A : Ty

  Kripke : (𝓥 𝓒 : Scoped) (PΓ : Ctx) (A : Ty) → Ctx → Set
  Kripke 𝓥 𝓒 PΓ A = □ ((PΓ ─Env) 𝓥 ─✴ 𝓒 A)

  record Semantics (d : System) (𝓥 𝓒 : Scoped) : Set where
    field
      th^𝓥 : Thinnable (𝓥 A)
      var : ∀[ 𝓥 A ⇒ 𝓒 A ]
      alg : ∀[ ⟦ d ⟧s (Kripke 𝓥 𝓒) A ⇒ 𝓒 A ]

    psh^𝓥 : IsPresheaf 𝓥
    psh^𝓥 QP v = th^𝓥 v (subuse-th QP)

    _─Comp : Ctx → Scoped → Ctx → Set
    (PΓ ─Comp) 𝓒 QΔ = ∀ {sz A} → Tm d sz A PΓ → 𝓒 A QΔ

    semantics : ∀ {PΓ QΔ} → (PΓ ─Env) 𝓥 QΔ → (PΓ ─Comp) 𝓒 QΔ
    body : ∀ {PΓ QΔ sz} → (PΓ ─Env) 𝓥 QΔ → ∀ {RΘ A} →
           Scope (Tm d sz) RΘ A PΓ → Kripke 𝓥 𝓒 RΘ A QΔ

    semantics ρ (`var v) =
      var (psh^𝓥 (⊴*-trans (ρ .sums)
                           (⊴*-trans (unrowL₂ (*ᴹ-mono (rowL₂ (v .basis))
                                                       ⊴ᴹ-refl))
                                     (getrowL₂ (1ᴹ-*ᴹ (ρ .M)) (v .idx))))
                 (ρ .lookup (plain-var v)))
    semantics {ctx P Γ} {ctx Q Δ} ρ (`con {sz = sz} t) =
      alg (map-s linRel {Scope (Tm d sz)} {Kripke 𝓥 𝓒} d
                 (λ {RΘ} {A} {P′} {Q′} r →
                   body {ctx P′ Γ} {ctx Q′ Δ} {sz} (pack (ρ .M) r (ρ .lookup)))
                 {_} {P} {Q} (ρ .sums)
                 t)
      where
      linRel : LinRel skewSemiring _ _
      linRel = record
        { rel = λ P Q → Q ⊴* unrow (row P *ᴹ ρ .M)
        ; rel-0ₘ = λ (sp0 , is-rel) →
          ⊴*-trans is-rel (unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp0) ⊴ᴹ-refl)
                                             (0ᴹ-*ᴹ (ρ .M))))
        ; rel-+ₘ = λ (sp+ , is-rel) →
          ⟨ ⊴*-refl , ⊴*-refl ⟩
            ⊴*-trans is-rel (unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp+) ⊴ᴹ-refl)
                                               (+ᴹ-*ᴹ _ _ (ρ .M))))
        ; rel-*ₘ = λ (sp* , is-rel) →
          ⊴*-refl ,
            ⊴*-trans is-rel (unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp*) ⊴ᴹ-refl)
                                               (*ₗ-*ᴹ _ _ (ρ .M))))
        }

    body ρ t {QΔ′} th .app✴ r σ =
      let ρ′ = th^Env th^𝓥 ρ th in
      semantics (++ᵉ (ρ′ ✴⟨ r ⟩ σ)) t
