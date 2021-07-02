{-# OPTIONS --safe --without-K --postfix-projections --prop #-}

open import Algebra.Po
open import Level

module Generic.Linear.Multicategory (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ) where

  open PoSemiring poSemiring

  open import Algebra.Relational
  open import Function.Base as F using (flip)
  open import Relation.Nary

  open import Generic.Linear.Algebra poSemiring
  import Generic.Linear.Syntax as Syntax
  import Generic.Linear.Variable as Variable
  import Generic.Linear.Environment as Environment

  record Multicategory ℓ e : Set (suc (ℓ ⊔ e)) where
    infix 4 _≈_ _⇒ˢ_
    infix 9 _∘_ _∘ˢ_

    field
      Obj : Set
    open Syntax Obj Carrier
    open Variable Obj rawPoSemiring
    open Environment Obj poSemiring

    field
      Hom : Scoped ℓ
      _≈_ : ∀ {Γ A} (f g : Hom Γ A) → Set e

    _⇒ˢ_ = [ Hom ]_⇒ᵉ_

    field
      id : ∀[ _∋_ ⇒ Hom ]
      _∘_ : ∀ {Γ Δ A} → Hom Δ A → Γ ⇒ˢ Δ → Hom Γ A

    -- TODO: move out into Extend, maybe.
    -- It duplicates Generic.Linear.Semantics.Syntactic.WithKit.1ᵏ
    idˢ : ∀ {Γ} → Γ ⇒ˢ Γ
    idˢ = pack 1ᴹ idAsLinRel ⊴*-refl
      λ le (lvar i q b) → id (lvar i q (⊴*-trans le b))

    _∘ˢ_ : ∀ {Γ Δ Θ} → Δ ⇒ˢ Θ → Γ ⇒ˢ Δ → Γ ⇒ˢ Θ
    σ ∘ˢ τ = pack (σ .M >>LinMor τ .M) (σ .asLinRel >>AsLinRel τ .asLinRel)
      (σ .sums , τ .sums)
      λ (leσ , leτ) v → σ .lookup leσ v ∘ record { [_]_⇒ᵉ_ τ; sums = leτ }

    field
      identityˡ : ∀ {Γ Δ A} (i : Δ ∋ A) (σ : Γ ⇒ˢ Δ) →
        id i ∘ σ ≈ σ .lookup (σ .sums) i
      identityʳ : ∀ {Γ A} (f : Hom Γ A) → f ∘ idˢ ≈ f
      assoc : ∀ {Γ Δ Θ A} (f : Hom Θ A) (σ : Δ ⇒ˢ Θ) (τ : Γ ⇒ˢ Δ) →
        f ∘ (σ ∘ˢ τ) ≈ (f ∘ σ) ∘ τ
      sym-assoc : ∀ {Γ Δ Θ A} (f : Hom Θ A) (σ : Δ ⇒ˢ Θ) (τ : Γ ⇒ˢ Δ) →
        (f ∘ σ) ∘ τ ≈ f ∘ (σ ∘ˢ τ)
