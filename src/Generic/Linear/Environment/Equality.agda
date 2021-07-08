{-# OPTIONS --safe --without-K --postfix-projections --prop #-}

open import Algebra.Po
open import Level

module Generic.Linear.Environment.Equality
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring renaming (Carrier to Ann; _≤_ to _⊴_)

  open import Data.LTree
  open import Data.LTree.Vector

  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Environment Ty poSemiring

  open import Data.Product as ×
  open import Data.Sum as ⊎
  open import Function using (id; _∘_)
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

  module _ {ℓ} {𝓥 : Scoped ℓ} where

    infix 4 [_]_∼ᵉ_

    record [_]_∼ᵉ_ {e} (_∼_ : ∀ {Γ A} → Rel (𝓥 Γ A) e)
           {Γ Δ} (ρ σ : [ 𝓥 ] Γ ⇒ᵉ Δ) : Set e where
      field
        M≈ : Mᴿ ρ .rel ⇔ Mᴿ σ .rel
        lookup≈ : ∀ {P′ Q′} {r : Mᴿ ρ .rel Q′ P′} {s : Mᴿ σ .rel Q′ P′} →
          r ≡ M≈ .proj₂ s ⊎ s ≡ M≈ .proj₁ r →
          ∀ {A} (i : _ ∋ A) → ρ .lookup r i ∼ σ .lookup s i
    open [_]_∼ᵉ_ public

    module _ {e} {_∼_ : ∀ {Γ A} → Rel (𝓥 Γ A) e} where

      private
        _∼ᵉ_ : ∀ {Γ Δ} → Rel ([ 𝓥 ] Γ ⇒ᵉ Δ) e
        _∼ᵉ_ = [ _∼_ ]_∼ᵉ_

      ∼ᵉ-refl :
        (∀ {Γ A} → Reflexive (_∼_ {Γ} {A})) →
        (∀ {Γ Δ} → Reflexive (_∼ᵉ_ {Γ} {Δ}))
      ∼ᵉ-refl refl .M≈ = id , id
      ∼ᵉ-refl refl .lookup≈ (inj₁ ≡.refl) i = refl
      ∼ᵉ-refl refl .lookup≈ (inj₂ ≡.refl) i = refl

      ∼ᵉ-trans :
        (∀ {Γ A} → Transitive (_∼_ {Γ} {A})) →
        (∀ {Γ Δ} → Transitive (_∼ᵉ_ {Γ} {Δ}))
      ∼ᵉ-trans trans p q .M≈ .proj₁ = q .M≈ .proj₁ ∘ p .M≈ .proj₁
      ∼ᵉ-trans trans p q .M≈ .proj₂ = p .M≈ .proj₂ ∘ q .M≈ .proj₂
      ∼ᵉ-trans trans p q .lookup≈ (inj₁ ≡.refl) i =
        trans (p .lookup≈ (inj₁ ≡.refl) i) (q .lookup≈ (inj₁ ≡.refl) i)
      ∼ᵉ-trans trans p q .lookup≈ (inj₂ ≡.refl) i =
        trans (p .lookup≈ (inj₂ ≡.refl) i) (q .lookup≈ (inj₂ ≡.refl) i)

      ∼ᵉ-sym :
        (∀ {Γ A} → Symmetric (_∼_ {Γ} {A})) →
        (∀ {Γ Δ} → Symmetric (_∼ᵉ_ {Γ} {Δ}))
      ∼ᵉ-sym sym p .M≈ = ×.swap (p .M≈)
      ∼ᵉ-sym sym p .lookup≈ (inj₁ x) i = sym (p .lookup≈ (inj₂ x) i)
      ∼ᵉ-sym sym p .lookup≈ (inj₂ y) i = sym (p .lookup≈ (inj₁ y) i)

      ∼ᵉ-isEquivalence :
        (∀ {Γ A} → IsEquivalence (_∼_ {Γ} {A})) →
        (∀ {Γ Δ} → IsEquivalence (_∼ᵉ_ {Γ} {Δ}))
      ∼ᵉ-isEquivalence e = record
        { refl = ∼ᵉ-refl (e .refl)
        ; sym = ∼ᵉ-sym (e .sym)
        ; trans = ∼ᵉ-trans (e .trans)
        } where open IsEquivalence
