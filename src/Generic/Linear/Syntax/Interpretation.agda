{-# OPTIONS --safe --without-K #-}

open import Algebra.Skew
open import Level using (0ℓ)
open import Relation.Binary using (Rel)

module Generic.Linear.Syntax.Interpretation
  (Ty : Set) (rawSkewSemiring : RawSkewSemiring 0ℓ 0ℓ)
  where

  open RawSkewSemiring rawSkewSemiring renaming (Carrier to Ann; _≤_ to _⊴_)

  open import Algebra using (Op₂; Opₗ)
  open import Data.Product as ×
  open import Data.Unit
  open import Function
  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary

  open import Data.LTree
  open import Data.LTree.Vector

  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Syntax Ty Ann

  open import Relation.Unary.Bunched
  private
    open module Dummy0 {s} = BunchedUnit (_⊴* 0* {s})
    open module Dummy+ {s} =
      BunchedConjunction (λ (R P Q : Vector _ s) → R ⊴* P +* Q)
    open module Dummy* {s} =
      BunchedScaling (λ (R : Vector _ s) r P → R ⊴* r *ₗ P)

  infixr 8 _─✴ᶜ_
  infixr 9 _✴ᶜ_
  infixr 10 _·ᶜ_

  ✴1ᶜ : Ctx → Set
  ✴1ᶜ (ctx R Γ) = ✴1 R

  _✴ᶜ_ : (T U : Ctx → Set) (RΓ : Ctx) → Set
  (T ✴ᶜ U) (ctx R Γ) = ((λ P → T (ctx P Γ)) ✴ (λ Q → U (ctx Q Γ))) R

  _─✴ᶜ_ : (T U : Ctx → Set) (RΓ : Ctx) → Set
  (T ─✴ᶜ U) (ctx R Γ) = ((λ P → T (ctx P Γ)) ─✴ (λ Q → U (ctx Q Γ))) R

  _·ᶜ_ : (ρ : Ann) (T : Ctx → Set) (RΓ : Ctx) → Set
  (ρ ·ᶜ T) (ctx R Γ) = (ρ · (λ P → T (ctx P Γ))) R

  {-
  record Dup (T : Ctx → Set) (RΓ : Ctx) : Set where
    constructor □⟨_,_⟩_
    open Ctx RΓ
    field
      split-0 : R ⊴* 0*
      split-+ : R ⊴* R +* R
      T-prf : T RΓ
  -}

  module WithScope (⟦_⊢_⟧ : Ctx → Scoped) where

    ⟦_⟧p′ : Premises → Ctx → Set
    ⟦ Γ `⊢ A ⟧p′ = ⟦ Γ ⊢ A ⟧
    ⟦ `⊤ ⟧p′ = U
    ⟦ `I ⟧p′ = ✴1ᶜ
    ⟦ p `∧ q ⟧p′ = ⟦ p ⟧p′ ∩ ⟦ q ⟧p′
    ⟦ p `* q ⟧p′ = ⟦ p ⟧p′ ✴ᶜ ⟦ q ⟧p′
    ⟦ ρ `· p ⟧p′ = ρ ·ᶜ ⟦ p ⟧p′
    -- ⟦ `□ p ⟧p′ = Dup (⟦ p ⟧p′)

    ⟦_⟧r′ : Rule → Scoped
    ⟦ rule ps A′ ⟧r′ A = const (A′ ≡ A) ∩ ⟦ ps ⟧p′

    ⟦_⟧s′ : System → Scoped
    ⟦ system L rs ⟧s′ A PΓ = Σ[ l ∈ L ] ⟦ rs l ⟧r′ A PΓ

  ⟦_⟧p : Premises → (Ctx → Scoped) → (Ctx → Set)
  ⟦ ps ⟧p Sc = let open WithScope Sc in ⟦ ps ⟧p′

  ⟦_⟧r : Rule → (Ctx → Scoped) → Scoped
  ⟦ r ⟧r Sc = let open WithScope Sc in ⟦ r ⟧r′

  ⟦_⟧s : System → (Ctx → Scoped) → Scoped
  ⟦ s ⟧s Sc = let open WithScope Sc in ⟦ s ⟧s′
