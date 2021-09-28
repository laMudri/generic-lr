{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Po
open import Level hiding (lift)

module Generic.Linear.Environment.Categorical
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring renaming (Carrier to Ann)

  open import Algebra.Relational
  open import Function.Base using (id)
  open import Relation.Nary

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Ty Ann hiding ([_]ᶜ)
  open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Environment Ty poSemiring
  open import Generic.Linear.Renaming Ty poSemiring

  record IdentityEnv {v} (𝓥 : OpenFam v) : Set (suc 0ℓ ⊔ v) where
    field
      pure : ∀[ _∋_ ⇒ 𝓥 ]

    subuse^Env : ∀ {s P Q γ} → P ≤* Q → [ 𝓥 ] ctx P γ ⇒ᵉ ctx {s} Q γ
    subuse^Env PQ .Ψ = 1ᴿ
    subuse^Env PQ .sums = PQ
    subuse^Env PQ .lookup r (lvar i q b) = pure (lvar i q (≤*-trans r b))

    id^Env : ∀ {Γ} → [ 𝓥 ] Γ ⇒ᵉ Γ
    id^Env = subuse^Env ≤*-refl
  open IdentityEnv {{...}} public

  instance
    identityEnv-∋ : IdentityEnv _∋_
    identityEnv-∋ .pure = id

  record ComposeEnv {u v w} (𝓤 : OpenFam u) (𝓥 : OpenFam v) (𝓦 : OpenFam w)
         : Set (suc 0ℓ ⊔ u ⊔ v ⊔ w) where
    field
      lift : ∀ {s t P Q γ δ} (ρ : [ 𝓤 ] ctx {s} P γ ⇒ᵉ ctx {t} Q δ) →
        ∀ {P′ Q′} → ρ .Ψ .rel Q′ P′ → ∀[ 𝓥 (ctx Q′ δ) ⇒ 𝓦 (ctx P′ γ) ]

    >>^Env : ∀ {Γ Δ Θ} → [ 𝓤 ] Γ ⇒ᵉ Δ → [ 𝓥 ] Δ ⇒ᵉ Θ → [ 𝓦 ] Γ ⇒ᵉ Θ
    >>^Env ρ σ .Ψ = σ .Ψ >>ᴿ ρ .Ψ
    >>^Env ρ σ .sums = σ .sums , ρ .sums
    >>^Env ρ σ .lookup (s , r) v = lift ρ r (σ .lookup s v)
  open ComposeEnv {{...}} public

  instance
    composeEnv-𝓥-∋ : ∀ {v} {𝓥 : OpenFam v} → ComposeEnv 𝓥 _∋_ 𝓥
    composeEnv-𝓥-∋ .lift ρ r v = ρ .lookup r v

  postren^Env : ∀ {v} {𝓥 : OpenFam v} {Γ Δ Θ} →
    [ 𝓥 ] Γ ⇒ᵉ Δ → Δ ⇒ʳ Θ → [ 𝓥 ] Γ ⇒ᵉ Θ
  postren^Env = >>^Env
