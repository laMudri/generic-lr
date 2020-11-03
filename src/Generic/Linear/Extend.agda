{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ)

module Generic.Linear.Extend
  (Ty : Set) (skewSemiring : SkewSemiring 0ℓ 0ℓ)
  where

  open SkewSemiring skewSemiring
    renaming (Carrier to Ann
             ; _≤_ to _⊴_
             ; refl to ⊴-refl; trans to ⊴-trans
             )

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.Product
  open import Function.Base
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Algebra skewSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Environment Ty rawSkewSemiring
    renaming (var to ivar)
  open import Generic.Linear.Environment.Recursive Ty rawSkewSemiring
  open _─Env

  open import Relation.Unary.Bunched hiding (✴1⟨_⟩; _✴⟨_⟩_; ⟨_⟩·_; lam✴; app✴)
  private
    open module Dummy0 {s} = BunchedUnit (_⊴* 0* {s})
    open module Dummy+ {s} =
      BunchedConjunction (λ (R P Q : Vector _ s) → R ⊴* P +* Q)
    open module Dummy* {s} =
      BunchedScaling (λ (R : Vector _ s) r P → R ⊴* r *ₗ P)

  -- Classes for extensions by 0-use contexts

  record LeftExtend (𝓥 : Scoped) : Set where
    constructor mk
    field
      embedVarˡ : ∀ {s u Γ Θ A} (v : Var A Θ) →
                 𝓥 A (ctx {s} 0* Γ ++ᶜ ctx {u} (1ᴹ (v .idx)) Θ)

    extendˡ : ∀ {RΘ s Γ} → (RΘ ─Env) 𝓥 (ctx {s} 0* Γ ++ᶜ RΘ)
    extendˡ .M = [ 0ᴹ │ 1ᴹ ]
    extendˡ {ctx R Θ} .sums = unrowL₂ (*ᴹ-0ᴹ (row R)) ++₂ unrowL₂ (*ᴹ-1ᴹ _)
    extendˡ .lookup = embedVarˡ

    -- extendˡᵣ : ∀ {u R Θ s Γ} → let RΘ = ctx {u} R Θ in
    --            (RΘ ─Envᵣ) 𝓥 (ctx {s} 0* Γ ++ᶜ RΘ)
    -- extendˡᵣ {[-]} =
    --   ⟨_⟩·_
    --     ((mk λ i → annihil .proj₂ _) ++₂ [ *.identity .proj₂ _ ]₂)
    --     (embedVarˡ (ivar here refl))
    -- extendˡᵣ {ε} = ✴1⟨ ⊴*-refl ++₂ []₂ ⟩
    -- extendˡᵣ {t <+> u} {R} {Θ} {s} {Γ} =
    --   _✴⟨_⟩_ {y = 0* ++ (R ∘ ↙ ++ 0*)} {0* ++ (0* ++ R ∘ ↘)}
    --     {!!}
    --     ((mk λ _ → +.identity-← .proj₁ 0#) ++₂
    --       {!!})
    --     {!!}
  open LeftExtend {{...}} public

  record RightExtend (𝓥 : Scoped) : Set where
    constructor mk
    field
      embedVarʳ : ∀ {s u Γ Θ A} (v : Var A Θ) →
                 𝓥 A (ctx {u} (1ᴹ (v .idx)) Θ ++ᶜ ctx {s} 0* Γ)

    extendʳ : ∀ {RΘ s Γ} → (RΘ ─Env) 𝓥 (RΘ ++ᶜ ctx {s} 0* Γ)
    extendʳ .M = [ 1ᴹ │ 0ᴹ ]
    extendʳ {ctx R Θ} .sums = unrowL₂ (*ᴹ-1ᴹ _) ++₂ unrowL₂ (*ᴹ-0ᴹ (row R))
    extendʳ .lookup = embedVarʳ
  open RightExtend {{...}} public
