
{-# OPTIONS --safe --without-K #-}

open import Algebra.Po
open import Level using (Level; 0ℓ; _⊔_)
open import Relation.Binary using (Rel)

module Generic.Linear.Syntax.Interpretation
  (Ty : Set) (rawPoSemiring : RawPoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open RawPoSemiring rawPoSemiring renaming (Carrier to Ann)

  open import Algebra using (Op₂; Opₗ)
  open import Data.Bool.Base
  open import Data.Product as ×
  open import Data.Unit
  open import Function
  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary.Checked

  open import Data.LTree
  open import Data.LTree.Vector

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Syntax Ty Ann

  open import Relation.Unary.Bunched.Checked
  private
    open module Chk0 {s} = BunchedUnit (_≤0* {s})
    open module Chk+ {s} = BunchedConjunction (_≤[_+*_] {s})
      hiding (_─✴_)
    open module Chk* {s} = BunchedScaling (_≤[_*ₗ_] {s})
    open module ChkD {s} = BunchedDuplicable (_≤*_ {s}) _≤0* _≤[_+*_]
  import Relation.Unary.Bunched as Syn
  private
    open module Syn≤ {s} = Syn.BunchedOrder (_≤*_ {s})
    open module Syn+ {s} = Syn.BunchedConjunction (_≤[_+*_] {s})
      using (_─✴_)

  private
    variable
      ℓ t u : Level

  infix 4 _≤ᶜ_
  infixr 5 !!_
  infixr 8 _⇒ᵏᶜ_ _─✴ᶜ_
  infixr 9 _✴ᶜ_
  infixr 10 _·ᶜ_

  _≤ᶜ_ : (Γ Δ : Ctx) → Set
  ctx {s} P γ ≤ᶜ ctx {t} Q δ = Σ (s ≡ t) λ where
    refl → P ≤* Q × γ ≡ δ

  pattern !!_ PQ = refl , PQ , refl

  _⇒ᵏᶜ_ : (T : OpenType t) (U : OpenType u) (Γ : Ctx) → Set (t ⊔ u)
  (T ⇒ᵏᶜ U) (ctx R γ) = ((λ P → T (ctx P γ)) ⇒ᵏ (λ Q → U (ctx Q γ))) R

  ℑᶜ : OpenType ℓ
  ℑᶜ (ctx R γ) = ℑ R

  _✴ᶜ_ : (T U : OpenType ℓ) (Γ : Ctx) → Set ℓ
  (T ✴ᶜ U) (ctx R γ) = ((λ P → T (ctx P γ)) ✴ (λ Q → U (ctx Q γ))) R

  _─✴ᶜ_ : (T : OpenType t) (U : OpenType u) (Γ : Ctx) → Set (t ⊔ u)
  (T ─✴ᶜ U) (ctx R γ) = ((λ P → T (ctx P γ)) ─✴ (λ Q → U (ctx Q γ))) R

  _·ᶜ_ : (r : Ann) (T : OpenType ℓ) (Γ : Ctx) → Set ℓ
  (r ·ᶜ T) (ctx R γ) = (r · (λ P → T (ctx P γ))) R

  Dupᶜ : (T : OpenType ℓ) (Γ : Ctx) → Set ℓ
  Dupᶜ T (ctx R γ) = Dup (λ P → T (ctx P γ)) R




  ⟦_⟧p : Premises → ExtOpenFam ℓ → OpenType ℓ
  ⟦ ⟨ Δ `⊢ A ⟩ ⟧p X Γ = X Δ Γ A
  ⟦ `⊤ ⟧p X = U
  ⟦ p `∧ q ⟧p X = ⟦ p ⟧p X ∩ ⟦ q ⟧p X
  ⟦ `ℑ ⟧p X = ℑᶜ
  ⟦ p `✴ q ⟧p X = ⟦ p ⟧p X ✴ᶜ ⟦ q ⟧p X
  ⟦ r `· p ⟧p X = r ·ᶜ ⟦ p ⟧p X



  ⟦ `□ p ⟧p X = Dupᶜ (⟦ p ⟧p X)




  ⟦_⟧r : Rule → ExtOpenFam ℓ → OpenFam ℓ
  ⟦ ps =⇒ A′ ⟧r X Γ A = A′ ≡ A × ⟦ ps ⟧p X Γ





  ⟦_⟧s : System → ExtOpenFam ℓ → OpenFam ℓ
  ⟦ L ▹ rs ⟧s X Γ A = Σ[ l ∈ L ] ⟦ rs l ⟧r X Γ A
