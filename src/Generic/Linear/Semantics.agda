{-# OPTIONS --safe --sized-types --without-K --prop --postfix-projections #-}

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
  open import Data.Wrap
  open import Function using (Equivalence)
  open import Function.Extra
  open import Size
  open import Relation.Nary
  -- open import Relation.Unary hiding (_⊢_)
  open import Relation.Unary.Bunched

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring
  open import Generic.Linear.Syntax.Interpretation.Map Ty poSemiring
  open import Generic.Linear.Syntax.Term Ty rawPoSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Environment Ty poSemiring
  open import Generic.Linear.Renaming Ty poSemiring
  open import Generic.Linear.Renaming.Properties Ty poSemiring
  open import Generic.Linear.Environment.Properties Ty poSemiring

  private
    variable
      A : Ty
      ℓ v c : Level
      fl : PremisesFlags
      𝓥 : Scoped v
      𝓒 : Scoped c
      Θ : Ctx

  Kripke : (𝓥 : Scoped v) (𝓒 : Scoped c) → Ctx → Scoped _
  Kripke = Wrap λ 𝓥 𝓒 Γ Δ A → □ʳ (([ 𝓥 ]_⇒ᵉ Γ) ─✴ᶜ _⟨ 𝓒 ⟩⊢ A) Δ

  mapK𝓒 : ∀ {v c c′} {𝓥 : Scoped v} {𝓒 : Scoped c} {𝓒′ : Scoped c′} →
          ∀[ 𝓒 ⇒ 𝓒′ ] → ∀[ Kripke 𝓥 𝓒 ⇒ Kripke 𝓥 𝓒′ ]
  mapK𝓒 f b .get th .app✴ sp ρ = f (b .get th .app✴ sp ρ)

  record Semantics (d : System fl) (𝓥 : Scoped v) (𝓒 : Scoped c)
         : Set (suc 0ℓ ⊔ v ⊔ c) where
    field
      ren^𝓥 : Renameable (_⟨ 𝓥 ⟩⊢ A)
      var : ∀[                   𝓥 ⇒ 𝓒 ]
      alg : ∀[ ⟦ d ⟧s (Kripke 𝓥 𝓒) ⇒ 𝓒 ]

    psh^𝓥 : IsPresheaf 𝓥
    psh^𝓥 = ren⇒psh (λ {A} → ren^𝓥 {A})
    open With-psh^𝓥 psh^𝓥

    [_]_⇒ᶜ_ : (𝓒′ : Scoped ℓ) (Γ Δ : Ctx) → Set ℓ
    [ 𝓒′ ] Γ ⇒ᶜ Δ = ∀ {sz} → ∀[ [ d , sz ] Δ ⊢_ ⇒ 𝓒′ Γ ]

    semantics : ∀ {Γ Δ} → [ 𝓥 ] Γ ⇒ᵉ Δ → [ 𝓒 ] Γ ⇒ᶜ Δ
    body : ∀ {Γ Δ sz} → [ 𝓥 ] Γ ⇒ᵉ Δ → ∀ {Θ} →
      ∀[ Scope [ d , sz ]_⊢_ Θ Δ ⇒ Kripke 𝓥 𝓒 Θ Γ ]

    semantics ρ (`var v) = var (ρ .lookup (ρ .sums) v)
    semantics ρ (`con {sz = sz} t) =
      alg (map-s (ρ .M) d
        (λ r → body (record { [_]_⇒ᵉ_ ρ; sums = ρ .asLinRel .equiv .g r }))
        (sums-⊴* ρ) t)
      where open Equivalence

    body ρ t .get th .app✴ r σ =
      let ρ′ = ren^Env ren^𝓥 ρ th in
      semantics (++ᵉ (ρ′ ✴⟨ r ⟩ σ)) t
