{-# OPTIONS --safe --without-K --postfix-projections --prop #-}

open import Algebra.Po
open import Level hiding (lift)

module Generic.Linear.Environment.Equality
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring using (rawPoSemiring) renaming (Carrier to Ann)

  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Variable.Equality Ty rawPoSemiring
  open import Generic.Linear.Environment Ty poSemiring

  open import Algebra.Relational
  open import Data.Product as ×
  open import Data.Wrap
  open import Function using (id; _∘_; _on_; _-⟨_⟩-_; module Equivalence)
  open import Relation.Binary hiding (_⇒_)
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
  open import Relation.Binary.Setoid
  open import Relation.Nary

  Scoped= : ∀ ℓ e → Set (suc (ℓ ⊔ e))
  Scoped= ℓ e = Ctx → Ty → Setoid ℓ e

  module Scoped= {ℓ e} (𝓥 : Scoped= ℓ e) where
    private
      module 𝓥 Γ A = Setoid (𝓥 Γ A)
      module 𝓥I {Γ A} = 𝓥 Γ A
    open 𝓥 public using (Carrier)
    open 𝓥I public hiding (Carrier)

  record [_]_=⇒ᵉ_ {ℓ e} (𝓥 : Scoped= ℓ e) (Γ Δ : Ctx)
         : Set (suc 0ℓ ⊔ ℓ ⊔ e) where
    open Scoped= 𝓥
    field
      env : [ (λ Γ A → Carrier Γ A) ] Γ ⇒ᵉ Δ
      lookup-resp-idx : ∀ {P′ Q′ A r r′ i i′} → i ≈ᵛ i′ →
        _≈_ {A = A}
          (env .lookup {P′} {Q′} r i)
          (env .lookup {P′} {Q′} r′ i′)
  open [_]_=⇒ᵉ_ public

  module _ {ℓ ve} {𝓥 : Scoped= ℓ ve} where

    open Setoid

    infix 4 [_]_∼ᵉ_

    record [_]_∼ᵉ_ {e} (∼ : ∀ {Γ A} → Rel= (𝓥 Γ A) e)
           {Γ Δ} (ρ σ : [ 𝓥 ] Γ =⇒ᵉ Δ) : Set e where
      field
        M≈ : Mᴿ (ρ .env) .rel ⇔ Mᴿ (σ .env) .rel
        lookup≈ : ∀ {P′ Q′} r s {A} (i : _ ∋ A) →
          ∼ .rel (ρ .env .lookup {P′} {Q′} r i) (σ .env .lookup s i)
    open [_]_∼ᵉ_ public

    module _ {e} {∼ : ∀ {Γ A} → Rel= (𝓥 Γ A) e} where

      private
        _∼ᵉ_ : ∀ {Γ Δ} → Rel ([ 𝓥 ] Γ =⇒ᵉ Δ) e
        _∼ᵉ_ = [ ∼ ]_∼ᵉ_

      ∼ᵉ-refl :
        (∀ {Γ A} → Reflexive (∼ {Γ} {A} .rel)) →
        (∀ {Γ Δ} → Reflexive (_∼ᵉ_ {Γ} {Δ}))
      ∼ᵉ-refl refl .M≈ = id , id
      ∼ᵉ-refl refl∼ {x = ρ} .lookup≈ _ _ i =
        ∼ .resp-≈ (ρ .lookup-resp-idx ≈ᵛ-refl) (𝓥 _ _ .refl) refl∼

      ∼ᵉ-trans :
        (∀ {Γ A} → Transitive (∼ {Γ} {A} .rel)) →
        (∀ {Γ Δ} → Transitive (_∼ᵉ_ {Γ} {Δ}))
      ∼ᵉ-trans trans∼ p q .M≈ .proj₁ = q .M≈ .proj₁ ∘ p .M≈ .proj₁
      ∼ᵉ-trans trans∼ p q .M≈ .proj₂ = p .M≈ .proj₂ ∘ q .M≈ .proj₂
      ∼ᵉ-trans trans∼ {i = ρ} {σ} {τ} p q .lookup≈ {P′} {Q′} r t i =
        trans∼ (p .lookup≈ r s i) (q .lookup≈ s t i)
        where
        open Equivalence

        -- We could also have s = q .M≈ .proj₂ t, which may or may not help
        -- with some judgemental equalities.
        s : Mᴿ (σ .env) .rel Q′ P′
        s = p .M≈ .proj₁ r

      ∼ᵉ-sym :
        (∀ {Γ A} → Symmetric (∼ {Γ} {A} .rel)) →
        (∀ {Γ Δ} → Symmetric (_∼ᵉ_ {Γ} {Δ}))
      ∼ᵉ-sym sym p .M≈ = ×.swap (p .M≈)
      ∼ᵉ-sym sym p .lookup≈ r s i = sym (p .lookup≈ s r i)

      ∼ᵉ-isEquivalence :
        (∀ {Γ A} → IsEquivalence (∼ {Γ} {A} .rel)) →
        (∀ {Γ Δ} → IsEquivalence (_∼ᵉ_ {Γ} {Δ}))
      ∼ᵉ-isEquivalence e = record
        { refl = ∼ᵉ-refl (e .refl)
        ; sym = ∼ᵉ-sym (e .sym)
        ; trans = ∼ᵉ-trans (e .trans)
        } where open IsEquivalence

    _≈ᵉ_ : ∀ {Γ Δ} (ρ σ : [ 𝓥 ] Γ =⇒ᵉ Δ) → Set ve
    _≈ᵉ_ = [ ≈-Rel= (𝓥 _ _) ]_∼ᵉ_

  open import Generic.Linear.Environment.Categorical Ty poSemiring

  record IdentityEnv= {v e} (𝓥 : Scoped= v e) : Set (suc 0ℓ ⊔ v ⊔ e) where
    open Scoped= 𝓥
    field
      pure : ∀[ _∋_ ⇒ Carrier ]
      pure-resp-idx : ∀ {Γ A} → ∀[ _≈ᵛ_ {Γ} {A} ⇒ (_≈_ on pure) ]

    open IdentityEnv record { pure = pure }

    id^Env= : ∀ {Γ} → [ 𝓥 ] Γ =⇒ᵉ Γ
    id^Env= .env = id^Env
    id^Env= .lookup-resp-idx [ ii ] = pure-resp-idx [ ii ]

  record ComposeEnv= {u v w ue ve we}
         (𝓤 : Scoped= u ue) (𝓥 : Scoped= v ve) (𝓦 : Scoped= w we)
         : Set (suc 0ℓ ⊔ u ⊔ v ⊔ w ⊔ ue ⊔ ve ⊔ we) where
    private
      module 𝓤 = Scoped= 𝓤
      module 𝓥 = Scoped= 𝓥
      module 𝓦 = Scoped= 𝓦
    field
      lift : ∀ {s t P Q γ δ} (ρ : [ 𝓤.Carrier ] ctx {s} P γ ⇒ᵉ ctx {t} Q δ) →
        ∀ {P′ Q′} → Mᴿ ρ .rel Q′ P′ →
        ∀[ 𝓥.Carrier (ctx Q′ δ) ⇒ 𝓦.Carrier (ctx P′ γ) ]
      lift-resp-idx : ∀ {Γ Δ Θ}
        (ρ : [ 𝓤.Carrier ] Γ ⇒ᵉ Δ) (σ : [ 𝓥.Carrier ] Δ ⇒ᵉ Θ)
        {P′ Q′r Q′r′ r r′ Q′s s s′ A i i′} → i ≈ᵛ i′ →
        lift ρ {P′} {Q′r} r {A} (σ .lookup {Q′ = Q′s} s i)
          𝓦.≈ lift ρ {Q′ = Q′r′} r′ (σ .lookup s′ i′)

    open ComposeEnv record { lift = lift }

    >>^Env= : ∀ {Γ Δ Θ} → [ 𝓤 ] Γ =⇒ᵉ Δ → [ 𝓥 ] Δ =⇒ᵉ Θ → [ 𝓦 ] Γ =⇒ᵉ Θ
    >>^Env= ρ σ .env = >>^Env (ρ .env) (σ .env)
    >>^Env= ρ σ .lookup-resp-idx ii = lift-resp-idx (ρ .env) (σ .env) ii
