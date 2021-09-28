{-# OPTIONS --sized-types --without-K --prop --postfix-projections #-}

open import Algebra.Po
open import Level using (Level; 0ℓ; _⊔_; suc)

module Generic.Linear.Semantics
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring renaming (Carrier to Ann)

  open import Algebra.Po.Relation
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.Product
  open import Data.Wrap
  open import Function using (Equivalence; _$_)
  open import Function.Extra
  open import Size
  open import Relation.Nary
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
      𝓥 : OpenFam v
      𝓒 : OpenFam c
      Θ : Ctx

  Kripke : (𝓥 : OpenFam v) (𝓒 : OpenFam c) → ExtOpenFam _
  Kripke = Wrap λ 𝓥 𝓒 Δ Γ A → □ʳ ([ 𝓥 ]_⇒ᵉ Δ ─✴ᶜ [ 𝓒 ]_⊨ A) Γ

  mapK𝓒 : ∀ {v c c′} {𝓥 : OpenFam v} {𝓒 : OpenFam c} {𝓒′ : OpenFam c′} →
          ∀[ 𝓒 ⇒ 𝓒′ ] → ∀[ Kripke 𝓥 𝓒 ⇒ Kripke 𝓥 𝓒′ ]
  mapK𝓒 f b .get th .app✴ sp ρ = f (b .get th .app✴ sp ρ)

  record Semantics (d : System fl) (𝓥 : OpenFam v) (𝓒 : OpenFam c)
         : Set (suc 0ℓ ⊔ v ⊔ c) where
    field
      ren^𝓥 : ∀ {A} → Renameable ([ 𝓥 ]_⊨ A)
      ⟦var⟧ : ∀[                   𝓥 ⇒ 𝓒 ]
      ⟦con⟧ : ∀[ ⟦ d ⟧s (Kripke 𝓥 𝓒) ⇒ 𝓒 ]

    psh^𝓥 : IsPresheaf 𝓥
    psh^𝓥 = ren⇒psh (λ {A} → ren^𝓥 {A})
    open With-psh^𝓥 psh^𝓥

    [_]_⇒ᶜ_ : (𝓒′ : OpenFam ℓ) (Γ Δ : Ctx) → Set ℓ
    [ 𝓒′ ] Γ ⇒ᶜ Δ = ∀ {sz} → ∀[ [ d , sz ] Δ ⊢_ ⇒ [ 𝓒′ ] Γ ⊨_ ]

    semantics : ∀ {Γ Δ} → [ 𝓥 ] Γ ⇒ᵉ Δ → [ 𝓒 ] Γ ⇒ᶜ Δ
    body : ∀ {Γ Δ sz} → [ 𝓥 ] Γ ⇒ᵉ Δ → ∀ {Θ} →
      ∀[ Scope [ d , sz ]_⊢_ Θ Δ ⇒ Kripke 𝓥 𝓒 Θ Γ ]

    semantics ρ (`var v) = ⟦var⟧ $ ρ .lookup (ρ .sums) v
    semantics ρ (`con t) = ⟦con⟧ $
      map-s (ρ .Ψ) d
        (λ r → body (record { [_]_⇒ᵉ_ ρ; sums = r }))
        (ρ .sums) t
      where open Equivalence

    body ρ t .get th .app✴ r σ =
      let ρ′ = ren^Env ren^𝓥 ρ th in
      semantics (++ᵉ (ρ′ ✴⟨ r ⟩ σ)) t
