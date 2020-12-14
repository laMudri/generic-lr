{-# OPTIONS --safe --sized-types --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (Level; 0ℓ; _⊔_)

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
  open import Relation.Unary.Bunched

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
      ℓ v c : Level

  Kripke : (𝓥 : Scoped v) (𝓒 : Scoped c) (PΓ : Ctx) (A : Ty) →
           Ctx → Set (v ⊔ c)
  Kripke 𝓥 𝓒 PΓ A = □ ((PΓ ─Env) 𝓥 ─✴ᶜ 𝓒 A)

  mapK𝓒 : ∀ {v c c′} {𝓥 : Scoped v} {𝓒 : Scoped c} {𝓒′ : Scoped c′} →
          (∀ {A} → ∀[ 𝓒 A ⇒ 𝓒′ A ]) →
          ∀ {PΓ A} → ∀[ Kripke 𝓥 𝓒 PΓ A ⇒ Kripke 𝓥 𝓒′ PΓ A ]
  mapK𝓒 f b th .app✴ sp ρ = f (b th .app✴ sp ρ)

  record Semantics (d : System) (𝓥 : Scoped v) (𝓒 : Scoped c)
                   : Set (v ⊔ c) where
    field
      th^𝓥 : Thinnable (𝓥 A)
      var : ∀[ 𝓥 A ⇒ 𝓒 A ]
      alg : ∀[ ⟦ d ⟧s (Kripke 𝓥 𝓒) A ⇒ 𝓒 A ]

    psh^𝓥 : IsPresheaf 𝓥
    psh^𝓥 QP v = th^𝓥 v (subuse-th QP)

    _─Comp : Ctx → Scoped ℓ → Ctx → Set ℓ
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
      alg (map-s linMor {X = Scope (Tm d sz)} {Y = Kripke 𝓥 𝓒} d
                 (λ {RΘ} {A} {P′} {Q′} r →
                   body {ctx P′ Γ} {ctx Q′ Δ} {sz} (pack (ρ .M) r (ρ .lookup)))
                 {_} {P} {Q} (ρ .sums)
                 t)
      where
      open SkewLeftSemimoduleMor
      open ProsetMor

      linMor : LinMor skewSemiring _ _
      linMor .prosetMor .apply P = unrow (row P *ᴹ ρ .M)
      linMor .prosetMor .hom-mono PP = unrowL₂ (*ᴹ-mono (rowL₂ PP) ⊴ᴹ-refl)
      linMor .hom-0ₘ = unrowL₂ (0ᴹ-*ᴹ (ρ .M))
      linMor .hom-+ₘ P Q = unrowL₂ (+ᴹ-*ᴹ _ _ (ρ .M))
      linMor .hom-*ₘ r P = unrowL₂ (*ₗ-*ᴹ _ _ (ρ .M))
      -- linRel : LinRel skewSemiring _ _
      -- linRel = record
      --   { rel = λ P Q → Q ⊴* unrow (row P *ᴹ ρ .M)
      --   ; rel-0ₘ = λ (sp0 , is-rel) →
      --     ⊴*-trans is-rel (unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp0) ⊴ᴹ-refl)
      --                                        (0ᴹ-*ᴹ (ρ .M))))
      --   ; rel-+ₘ = λ (sp+ , is-rel) →
      --     ⟨ ⊴*-refl , ⊴*-refl ⟩
      --       ⊴*-trans is-rel (unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp+) ⊴ᴹ-refl)
      --                                          (+ᴹ-*ᴹ _ _ (ρ .M))))
      --   ; rel-*ₘ = λ (sp* , is-rel) →
      --     ⊴*-refl ,
      --       ⊴*-trans is-rel (unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp*) ⊴ᴹ-refl)
      --                                          (*ₗ-*ᴹ _ _ (ρ .M))))
      --   }

    body ρ t {QΔ′} th .app✴ r σ =
      let ρ′ = th^Env th^𝓥 ρ th in
      semantics (++ᵉ (ρ′ ✴⟨ r ⟩ σ)) t
