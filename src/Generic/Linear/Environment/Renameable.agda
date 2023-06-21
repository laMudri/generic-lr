{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Po
open import Function.Base using (flip; _∘_)
open import Level using (Level; 0ℓ)
open import Relation.Binary using (Rel; IsPreorder; Reflexive; Transitive)
import Generic.Linear.Syntax as Syntax
import Generic.Linear.Renaming as Renaming

module Generic.Linear.Environment.Renameable
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  (open PoSemiring poSemiring renaming (Carrier to Ann))
  (open Syntax Ty Ann) (open Renaming Ty poSemiring)
  {v} (_𝓥⊨_ : OpenFam v) (ren^𝓥 : ∀ {A} → Renameable (_𝓥⊨ A))
  where

  open import Algebra.Relational
  open import Data.Product
  open import Data.Sum
  open import Function.Base using (id; _$_)
  open import Function.Extra
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)
  open import Relation.Unary
  open import Relation.Unary.Bunched using (_✴⟨_⟩_)

  open import Data.LTree
  open import Data.LTree.Vector

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring
  open import Generic.Linear.Environment Ty poSemiring as Env hiding ([_]_⇒ᵉ_)
  open import Generic.Linear.Environment.Properties Ty poSemiring
  open import Generic.Linear.Environment.Categorical Ty poSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Renaming.Properties Ty poSemiring
  open import Generic.Linear.Renaming.Monoidal Ty poSemiring

  open With-psh^𝓥 {𝓥 = _𝓥⊨_} (ren⇒psh ren^𝓥)

  private
    infix 20 _⇒ᵉ_
    _⇒ᵉ_ = Env.[ _𝓥⊨_ ]_⇒ᵉ_

  infix 50 _++⇒++′_ _++⇒++_

  []⇒[]′ : ∀ {Γ Δ : SizedCtx ε} → sctx→ctx Γ ⇒ᵉ sctx→ctx Δ
  []⇒[]′ = []ᵉ′ ℑᶜ⟨ []ₙ ⟩

  []⇒[] : []ᶜ ⇒ᵉ []ᶜ
  []⇒[] = []⇒[]′

  _++⇒++′_ : ∀ {sΓ tΓ sΔ tΔ}
    {Γ : SizedCtx (sΓ <+> tΓ)} {Δ : SizedCtx (sΔ <+> tΔ)} →
    leftᶜ′ Γ ⇒ᵉ leftᶜ′ Δ → rightᶜ′ Γ ⇒ᵉ rightᶜ′ Δ → sctx→ctx Γ ⇒ᵉ sctx→ctx Δ
  ρ ++⇒++′ σ = ++ᵉ′ $
    ren^Env ren^𝓥 ρ (↙ʳ′ 0*-triv)
      ✴⟨ mkᶜ {P = _ ++ _} {_ ++ _} (+*-identity↘ _ ++ₙ +*-identity↙ _) ⟩
    ren^Env ren^𝓥 σ (↘ʳ′ 0*-triv)

  _++⇒++_ : ∀ {Γl Γr Δl Δr} →
    Γl ⇒ᵉ Δl → Γr ⇒ᵉ Δr → Γl ++ᶜ Γr ⇒ᵉ Δl ++ᶜ Δr
  ρ ++⇒++ σ = ρ ++⇒++′ σ

  pw-env : ∀ {s γ δ P Q} → (∀ i → (Q i · (_𝓥⊨ δ i)) [ P i ∙ γ i ]ᶜ) →
    ctx {s} P γ ⇒ᵉ ctx {s} Q δ
  pw-env {[-]} {γ} {δ} {P} {Q} f = [-]ᵉ′ go
    where
    go : (Q here · _𝓥⊨ δ here) (ctx P γ)
    go with f here
    ... | ⟨ sp* ⟩·ᶜ v =
      ⟨ mkᶜ {Q = [ _ ]} [ sp* .get here ]ₙ ⟩· ren^𝓥 v ρ
      where
      ρ : _ ⇒ʳ _
      ρ .Ψ = 1ᴿ
      ρ .fit-here = [ ≤-refl ]ₙ
      ρ .lookup r (lvar i q b) with here ← i = lvar here q (≤*-trans r b)
  pw-env {ε} f = []⇒[]′
  pw-env {s <+> t} f = pw-env (f ∘ ↙) ++⇒++′ pw-env (f ∘ ↘)
