{-# OPTIONS --sized-types --without-K --prop --postfix-projections #-}

open import Algebra.Po
open import Level

module Generic.Linear.Semantics.Syntactic
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring renaming (Carrier to Ann)

  open import Algebra.Po.Relation
  open import Algebra.Relational
  open import Data.LTree
  open import Data.LTree.Vector hiding ([]ˢ)
  open import Data.Product
  open import Data.Wrap renaming ([_] to mk)
  open import Function.Base using (id; _∘_; _$_)
  open import Function.Extra
  open import Size
  open import Relation.Nary
  open import Relation.Unary.Bunched
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)

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
  open import Generic.Linear.Environment.Categorical Ty poSemiring
  open import Generic.Linear.Semantics Ty poSemiring

  infix 20 [_]_⇒ˢ_

  private
    variable
      fl : PremisesFlags
      d : System fl
      A : Ty
      v c : Level
      𝓥 : OpenFam v
      𝓒 : OpenFam c
      Γ Δ Θ : Ctx

  record Kit (d : System fl) (𝓥 : OpenFam v) : Set (suc 0ℓ ⊔ v) where
    field
      ren^𝓥 : ∀ {A} → Renameable ([ 𝓥 ]_⊨ A)
      vr : ∀[ _∋_ ⇒ 𝓥 ]
      tm : ∀[ 𝓥 ⇒ [ d , ∞ ]_⊢_ ]

    psh^𝓥 : IsPresheaf 𝓥
    psh^𝓥 = ren⇒psh (λ {A} → ren^𝓥 {A})

    instance
      identityEnv : IdentityEnv 𝓥
      identityEnv .pure = vr

  open Semantics

  reify : {{IdentityEnv 𝓥}} → ∀[ Kripke 𝓥 𝓒 ⇒ Scope 𝓒 ]
  reify b =
    b .get ↙ʳ .app✴ (+*-identity↘ _ ++ₙ +*-identity↙ _) (>>^Env id^Env ↘ʳ)

  module _ where
    open Kit

    kit→sem : Kit d 𝓥 → Semantics d 𝓥 [ d , ∞ ]_⊢_
    kit→sem K .ren^𝓥 = K .ren^𝓥
    kit→sem K .⟦var⟧ = K .tm
    kit→sem {d = d} K .⟦con⟧ = `con ∘ map-s′ d reify
      where open Kit K using (identityEnv)

  Ren-Kit : Kit d _∋_
  Ren-Kit = record { ren^𝓥 = ren^∋ ; vr = id ; tm = `var }

  Ren : Semantics d _∋_ [ d , ∞ ]_⊢_
  Ren = kit→sem Ren-Kit

  ren : Γ ⇒ʳ Δ → [ d , ∞ ] Δ ⊢ A → [ d , ∞ ] Γ ⊢ A
  ren ρ t = semantics Ren ρ t

  ren^⊢ : Renameable ([ d , ∞ ]_⊢ A)
  ren^⊢ t ρ = ren ρ t

  psh^⊢ : IsPresheaf [ d , ∞ ]_⊢_
  psh^⊢ = ren⇒psh (λ {A} → ren^⊢ {A = A})

  instance
    identityEnv^⊢ : IdentityEnv [ d , ∞ ]_⊢_
    identityEnv^⊢ .pure = `var

  Sub-Kit : Kit d [ d , ∞ ]_⊢_
  Sub-Kit = record { ren^𝓥 = ren^⊢ ; vr = `var ; tm = id }

  Sub : Semantics d [ d , ∞ ]_⊢_ [ d , ∞ ]_⊢_
  Sub = kit→sem Sub-Kit

  [_]_⇒ˢ_ : (d : System fl) (Γ Δ : Ctx) → Set₁
  [ d ] Γ ⇒ˢ Δ = [ [ d , ∞ ]_⊢_ ] Γ ⇒ᵉ Δ

  sub : [ d ] Γ ⇒ˢ Δ → [ d , ∞ ] Δ ⊢ A → [ d , ∞ ] Γ ⊢ A
  sub σ t = semantics Sub σ t

  -- _>>ˢ_ : Substitution d Γ Δ → Substitution d Δ Θ → Substitution d Γ Θ
  -- (ρ >>ˢ σ) .M = ρ .M *ᴹ σ .M
  -- (ρ >>ˢ σ) .sums = {!!}
  -- (ρ >>ˢ σ) .lookup v = psh^Tm {!!} (sub σ (psh^Tm (≤*-trans (ρ .sums) {!!}) (ρ .lookup v)))

  module WithKit (K : Kit d 𝓥) where
    private
      module K = Kit K
    open With-psh^𝓥 (λ {_} {γ} → K.psh^𝓥 {γ = γ})

    infix 5 _++ᵏ_

    1ᵏ : [ 𝓥 ] Γ ⇒ᵉ Γ
    1ᵏ = id^Env

    []ᵏ : [ 𝓥 ] []ᶜ ⇒ᵉ []ᶜ
    []ᵏ = []ᵉ ℑ⟨ []ₙ ⟩

    _++ᵏ_ : ∀ {Γl Δl Γr Δr} →
      [ 𝓥 ] Γl ⇒ᵉ Δl → [ 𝓥 ] Γr ⇒ᵉ Δr → [ 𝓥 ] Γl ++ᶜ Γr ⇒ᵉ Δl ++ᶜ Δr
    ρ ++ᵏ σ = ++ᵉ $
      ren^Env K.ren^𝓥 ρ ↙ʳ
        ✴⟨ (+*-identity↘ _ ++ₙ +*-identity↙ _) ⟩
      ren^Env K.ren^𝓥 σ ↘ʳ

    [_·_]ᵏ : ∀ {r s A B} →
      r ≤ s → 𝓥 [ 1# · A ]ᶜ B → [ 𝓥 ] [ r · A ]ᶜ ⇒ᵉ [ s · B ]ᶜ
    [ le · t ]ᵏ = [-]ᵉ (⟨ [ ≤-trans le (*.identity .proj₂ _) ]ₙ ⟩· t)

  module _ {fl d} where
    open WithKit (Sub-Kit {fl} {d})

    infix 5 _++ˢ_

    1ˢ : [ d ] Γ ⇒ˢ Γ
    1ˢ = 1ᵏ

    []ˢ : [ d ] []ᶜ ⇒ˢ []ᶜ
    []ˢ = []ᵏ

    _++ˢ_ : ∀ {Γl Δl Γr Δr} →
      [ d ] Γl ⇒ˢ Δl → [ d ] Γr ⇒ˢ Δr → [ d ] Γl ++ᶜ Γr ⇒ˢ Δl ++ᶜ Δr
    _++ˢ_ = _++ᵏ_

    [_·_]ˢ : ∀ {r s A B} →
      r ≤ s → [ d , ∞ ] [ 1# · A ]ᶜ ⊢ B → [ d ] [ r · A ]ᶜ ⇒ˢ [ s · B ]ᶜ
    [_·_]ˢ = [_·_]ᵏ
