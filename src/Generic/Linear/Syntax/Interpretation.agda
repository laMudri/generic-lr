{-# OPTIONS --safe --without-K #-}

open import Algebra.Skew
open import Level using (Level; 0ℓ; _⊔_)
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
  open import Relation.Unary as Syn using ()
  open import Relation.Unary.Checked

  open import Data.LTree
  open import Data.LTree.Vector

  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Syntax Ty Ann

  open import Relation.Unary.Bunched.Checked
  private
    open module Chk0 {s} = BunchedUnit (_⊴* 0* {s})
    open module Chk+ {s} =
      BunchedConjunction (λ (R P Q : Vector _ s) → R ⊴* P +* Q)
        hiding (_─✴_)
    open module Chk* {s} =
      BunchedScaling (λ (R : Vector _ s) r P → R ⊴* r *ₗ P)
  import Relation.Unary.Bunched as Syn
  private
    open module Syn+ {s} =
      Syn.BunchedConjunction (λ (R P Q : Vector _ s) → R ⊴* P +* Q)
        using (_─✴_)

  private
    variable
      ℓ t u : Level

  infixr 8 _─✴ᶜ_
  infixr 9 _✴ᶜ_
  infixr 10 _·ᶜ_

  ✴1ᶜ : Ctx → Set ℓ
  ✴1ᶜ (ctx R Γ) = ✴1 R

  _✴ᶜ_ : (T U : Ctx → Set ℓ) (RΓ : Ctx) → Set ℓ
  (T ✴ᶜ U) (ctx R Γ) = ((λ P → T (ctx P Γ)) ✴ (λ Q → U (ctx Q Γ))) R

  _─✴ᶜ_ : (T : Ctx → Set t) (U : Ctx → Set u) (RΓ : Ctx) → Set (t ⊔ u)
  (T ─✴ᶜ U) (ctx R Γ) = ((λ P → T (ctx P Γ)) ─✴ (λ Q → U (ctx Q Γ))) R

  _·ᶜ_ : (ρ : Ann) (T : Ctx → Set ℓ) (RΓ : Ctx) → Set ℓ
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

  module WithScope (⟦_⊢_⟧ : Ctx → Scoped ℓ) where

    ⟦_⟧p′ : Premises → Ctx → Set ℓ
    ⟦ Γ `⊢ A ⟧p′ = ⟦ Γ ⊢ A ⟧
    ⟦ `⊤ ⟧p′ = U
    ⟦ `I ⟧p′ = ✴1ᶜ
    ⟦ p `∧ q ⟧p′ = ⟦ p ⟧p′ ∩ ⟦ q ⟧p′
    ⟦ p `* q ⟧p′ = ⟦ p ⟧p′ ✴ᶜ ⟦ q ⟧p′
    ⟦ ρ `· p ⟧p′ = ρ ·ᶜ ⟦ p ⟧p′
    -- ⟦ `□ p ⟧p′ = Dup (⟦ p ⟧p′)

    ⟦_⟧r′ : Rule → Scoped ℓ
    ⟦ rule ps A′ ⟧r′ A = const (A′ ≡ A) Syn.∩ ⟦ ps ⟧p′

    ⟦_⟧s′ : System → Scoped ℓ
    ⟦ system L rs ⟧s′ A PΓ = Σ[ l ∈ L ] ⟦ rs l ⟧r′ A PΓ

  ⟦_⟧p : Premises → (Ctx → Scoped ℓ) → (Ctx → Set ℓ)
  ⟦ ps ⟧p Sc = let open WithScope Sc in ⟦ ps ⟧p′

  ⟦_⟧r : Rule → (Ctx → Scoped ℓ) → Scoped ℓ
  ⟦ r ⟧r Sc = let open WithScope Sc in ⟦ r ⟧r′

  ⟦_⟧s : System → (Ctx → Scoped ℓ) → Scoped ℓ
  ⟦ s ⟧s Sc = let open WithScope Sc in ⟦ s ⟧s′
