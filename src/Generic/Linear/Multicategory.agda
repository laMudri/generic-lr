{-# OPTIONS --safe --without-K --postfix-projections --prop #-}

open import Algebra.Po
open import Level

module Generic.Linear.Multicategory (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ) where

  open PoSemiring poSemiring using (Carrier; rawPoSemiring)

  open import Algebra.Relational
  open import Data.Product
  open import Data.Sum
  open import Function.Base as F using (flip)
  open import Relation.Nary as R hiding (_⇒_)
  open import Relation.Binary using (Rel; Setoid; IsEquivalence)
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

  open import Generic.Linear.Algebra poSemiring hiding (equiv)
  import Generic.Linear.Syntax as Syntax
  import Generic.Linear.Variable as Variable
  import Generic.Linear.Environment as Environment
  import Generic.Linear.Environment.Equality as EnvironmentE

  record Multicategory ℓ e : Set (suc (ℓ ⊔ e)) where
    infix 4 _⇒_ _⇒ˢ_ _≈_ _≈ˢ_
    infix 9 _∘_ _∘ˢ_

    field
      Obj : Set
    open Syntax Obj Carrier
    open Variable Obj rawPoSemiring
    open Environment Obj poSemiring
    open EnvironmentE Obj poSemiring

    field
      _⇒_ : Scoped ℓ
      _≈_ : ∀ {Γ A} → Rel (_⇒_ Γ A) e

    _⇒ˢ_ = [ _⇒_ ]_⇒ᵉ_

    _≈ˢ_ : ∀ {Γ Δ} → Rel (Γ ⇒ˢ Δ) e
    _≈ˢ_ = [ _≈_ ]_∼ᵉ_

    field
      id : ∀[ _∋_ R.⇒ _⇒_ ]
      _∘_ : ∀ {Γ Δ A} → Δ ⇒ A → Γ ⇒ˢ Δ → Γ ⇒ A

    -- TODO: move out into Extend, maybe.
    -- It duplicates Generic.Linear.Semantics.Syntactic.WithKit.1ᵏ
    idˢ : ∀ {Γ} → Γ ⇒ˢ Γ
    idˢ = pack 1ᴹ idAsLinRel ≤*-refl
      λ le (lvar i q b) → id (lvar i q (≤*-trans le b))

    _∘ˢ_ : ∀ {Γ Δ Θ} → Δ ⇒ˢ Θ → Γ ⇒ˢ Δ → Γ ⇒ˢ Θ
    σ ∘ˢ τ = pack (σ .M >>LinMor τ .M) (σ .asLinRel >>AsLinRel τ .asLinRel)
      (σ .sums , τ .sums)
      λ (leσ , leτ) v → σ .lookup leσ v ∘ record { [_]_⇒ᵉ_ τ; sums = leτ }

    field
      equiv : ∀ {Γ A} → IsEquivalence (_≈_ {Γ} {A})

      ∘-resp-≈ : ∀ {Γ Δ A} {f f′ : Δ ⇒ A} {σ σ′ : Γ ⇒ˢ Δ} →
        f ≈ f′ → σ ≈ˢ σ′ → f ∘ σ ≈ f′ ∘ σ′

      identityˡ : ∀ {Γ Δ A} (i : Δ ∋ A) (σ : Γ ⇒ˢ Δ) →
        id i ∘ σ ≈ σ .lookup (σ .sums) i
      identityʳ : ∀ {Γ A} (f : Γ ⇒ A) → f ∘ idˢ ≈ f
      assoc : ∀ {Γ Δ Θ A} (f : Θ ⇒ A) (σ : Δ ⇒ˢ Θ) (τ : Γ ⇒ˢ Δ) →
        f ∘ (σ ∘ˢ τ) ≈ (f ∘ σ) ∘ τ

    module Equiv {Γ A} = IsEquivalence (equiv {Γ} {A})
    open Equiv

    equivˢ : ∀ {Γ Δ} → IsEquivalence (_≈ˢ_ {Γ} {Δ})
    equivˢ = ∼ᵉ-isEquivalence equiv
    module Equivˢ {Γ Δ} = IsEquivalence (equivˢ {Γ} {Δ}) renaming
      ( refl to reflˢ; trans to transˢ; sym to symˢ; reflexive to reflexiveˢ
      ; isPartialEquivalence to isPartialEquivalenceˢ
      )
    open Equivˢ

    ∘ˢ-resp-≈ˢ : ∀ {Γ Δ Θ} {τ τ′ : Δ ⇒ˢ Θ} {σ σ′ : Γ ⇒ˢ Δ} →
      τ ≈ˢ τ′ → σ ≈ˢ σ′ → τ ∘ˢ σ ≈ˢ τ′ ∘ˢ σ′
    ∘ˢ-resp-≈ˢ p q .M≈ .proj₁ (t , s) = p .M≈ .proj₁ t , q .M≈ .proj₁ s
    ∘ˢ-resp-≈ˢ p q .M≈ .proj₂ (t , s) = p .M≈ .proj₂ t , q .M≈ .proj₂ s
    ∘ˢ-resp-≈ˢ p q .lookup≈ (inj₁ ≡.refl) i =
      ∘-resp-≈ (p .lookup≈ (inj₁ ≡.refl) i) record
        { M≈ = q .M≈ ; lookup≈ = q .lookup≈ }
    ∘ˢ-resp-≈ˢ p q .lookup≈ (inj₂ ≡.refl) i =
      ∘-resp-≈ (p .lookup≈ (inj₂ ≡.refl) i) record
        { M≈ = q .M≈ ; lookup≈ = q .lookup≈ }
