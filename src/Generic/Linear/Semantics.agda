
{-# OPTIONS --sized-types --without-K --postfix-projections #-}

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
      i j ℓ v c : Level
      I : Set i
      J : Set j




  Kripke : (𝓥 : OpenFam v) (𝓒 : I ─OpenFam c) → I ─ExtOpenFam _
  Kripke = Wrap λ 𝓥 𝓒 Δ Γ A → □ʳ ([ 𝓥 ]_⇒ᵉ Δ ─✴ᶜ [ 𝓒 ]_⊨ A) Γ




  mapK𝓒 :
    ∀ {v c c′} {𝓥 : OpenFam v} {𝓒 : I ─OpenFam c} {𝓒′ : J ─OpenFam c′} {A B} →
    ∀[ [ 𝓒 ]_⊨ A ⇒ [ 𝓒′ ]_⊨ B ] → ∀ {Δ Γ} → Kripke 𝓥 𝓒 Δ Γ A → Kripke 𝓥 𝓒′ Δ Γ B
  mapK𝓒 f b .get ren .app✴ sp ρ = f (b .get ren .app✴ sp ρ)




  record Semantics (d : System) (𝓥 : OpenFam v) (𝓒 : OpenFam c)
         : Set (suc 0ℓ ⊔ v ⊔ c) where
    field
      ren^𝓥  : ∀ {A} → Renameable ([ 𝓥 ]_⊨ A)
      ⟦var⟧  : ∀[ 𝓥                    ⇒ 𝓒 ]
      ⟦con⟧  : ∀[ ⟦ d ⟧s (Kripke 𝓥 𝓒)  ⇒ 𝓒 ]




    psh^𝓥 : IsPresheaf 𝓥
    psh^𝓥 = ren⇒psh (λ {A} → ren^𝓥 {A})
    open With-psh^𝓥 psh^𝓥

    open Equivalence




    extend : ∀ {Γ Δ Θ} → [ 𝓥 ] Γ ⇒ᵉ Δ → Kripke 𝓥 ([ 𝓥 ]_⇒ᵉ_) Θ Γ (Δ ++ᶜ Θ)
    extend ρ .get ren .app✴ sp σ = ++ᵉ (ren^Env ren^𝓥 ρ ren ✴⟨ sp ⟩ σ)





    [_]_⇒ᶜ_ : (𝓒′ : OpenFam ℓ) (Γ Δ : Ctx) → Set ℓ
    [ 𝓒′ ] Γ ⇒ᶜ Δ = ∀ {sz} → ∀[ [ d , sz ] Δ ⊢_ ⇒ [ 𝓒′ ] Γ ⊨_ ]





    semantics : ∀ {Γ Δ} → [ 𝓥 ] Γ ⇒ᵉ Δ → ∀ {sz} →
      ∀[ [ d , sz ] Δ ⊢_ ⇒ [ 𝓒 ] Γ ⊨_ ]
    body : ∀ {Γ Δ} → [ 𝓥 ] Γ ⇒ᵉ Δ → ∀ {sz Θ} →
      ∀[ Scope [ d , sz ]_⊢_ Θ Δ ⇒ Kripke 𝓥 𝓒 Θ Γ ]





    semantics ρ (`var v) = ⟦var⟧ $ ρ .lookup (ρ .fit-here) v
    semantics ρ (`con M) = ⟦con⟧ $
      map-s (ρ .Ψ) d (λ r → body (relocate ρ r)) (ρ .fit-here) M





    body ρ M = mapK𝓒 (λ σ → semantics σ M) (extend ρ)
