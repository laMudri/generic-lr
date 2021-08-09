{-# OPTIONS --safe --without-K --prop --postfix-projections #-}

open import Algebra.Po
open import Level hiding (lift)

module Generic.Linear.Environment.Categorical
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring renaming (Carrier to Ann)

  open import Algebra.Relational
  open import Relation.Nary

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Ty Ann hiding ([_]ᶜ)
  open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Environment Ty poSemiring
  open import Generic.Linear.Renaming Ty poSemiring

  record IdentityEnv {v} (𝓥 : Scoped v) : Set (suc 0ℓ ⊔ v) where
    field
      pure : ∀[ _∋_ ⇒ 𝓥 ]

    subuse^Env : ∀ {s P Q γ} → P ≤* Q → [ 𝓥 ] ctx P γ ⇒ᵉ ctx {s} Q γ
    subuse^Env PQ .M = 1ᴹ
    subuse^Env PQ .asLinRel = idAsLinRel
    subuse^Env PQ .sums = PQ
    subuse^Env PQ .lookup r (lvar i q b) = pure (lvar i q (≤*-trans r b))

    id^Env : ∀ {Γ} → [ 𝓥 ] Γ ⇒ᵉ Γ
    id^Env = subuse^Env ≤*-refl

  record ComposeEnv {u v w} (𝓤 : Scoped u) (𝓥 : Scoped v) (𝓦 : Scoped w)
         : Set (suc 0ℓ ⊔ u ⊔ v ⊔ w) where
    field
      lift : ∀ {s t P Q γ δ} (ρ : [ 𝓤 ] ctx {s} P γ ⇒ᵉ ctx {t} Q δ) →
        ∀ {P′ Q′} → Mᴿ ρ .rel Q′ P′ → ∀[ 𝓥 (ctx Q′ δ) ⇒ 𝓦 (ctx P′ γ) ]

    >>^Env : ∀ {Γ Δ Θ} → [ 𝓤 ] Γ ⇒ᵉ Δ → [ 𝓥 ] Δ ⇒ᵉ Θ → [ 𝓦 ] Γ ⇒ᵉ Θ
    >>^Env ρ σ .M = σ .M >>LinMor ρ .M
    >>^Env ρ σ .asLinRel = σ .asLinRel >>AsLinRel ρ .asLinRel
    >>^Env ρ σ .sums = σ .sums , ρ .sums
    >>^Env ρ σ .lookup (s , r) v = lift ρ r (σ .lookup s v)

  postren^Env : ∀ {v} {𝓥 : Scoped v} {Γ Δ Θ} →
    [ 𝓥 ] Γ ⇒ᵉ Δ → Δ ⇒ʳ Θ → [ 𝓥 ] Γ ⇒ᵉ Θ
  postren^Env = >>^Env λ where .lift ρ r v → ρ .lookup r v
    where open ComposeEnv
