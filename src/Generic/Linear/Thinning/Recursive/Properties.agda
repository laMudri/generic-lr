{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ)

module Generic.Linear.Thinning.Recursive.Properties
  (Ty : Set) (skewSemiring : SkewSemiring 0ℓ 0ℓ)
  where

  open SkewSemiring skewSemiring
    renaming (Carrier to Ann; _≤_ to _⊴_; refl to ⊴-refl; trans to ⊴-trans)

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.Product
  open import Function.Base using (_∘_)
  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary hiding (U)

  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Algebra skewSemiring
  open import Generic.Linear.Syntax Ty Ann hiding ([_]ᶜ)
  open import Generic.Linear.Syntax.Interpretation Ty rawSkewSemiring
  open import Generic.Linear.Extend Ty skewSemiring
  open import Generic.Linear.Environment Ty rawSkewSemiring
    using (IsPresheaf; Var; var; idx; tyq)
  open import Generic.Linear.Environment.Recursive Ty rawSkewSemiring
  open import Generic.Linear.Thinning.Recursive Ty rawSkewSemiring

  open import Relation.Unary.Bunched hiding (✴1⟨_⟩; _✴⟨_⟩_; ⟨_⟩·_; lam✴; app✴)
  private
    open module Dummy0 {s} = BunchedUnit (_⊴* 0* {s})
    open module Dummy+ {s} =
      BunchedConjunction (λ (R P Q : Vector _ s) → R ⊴* P +* Q)
    open module Dummy* {s} =
      BunchedScaling (λ (R : Vector _ s) r P → R ⊴* r *ₗ P)
  open import Relation.Unary.Bunched.Properties
  private
    open module DummyCommMon {s} = BunchedCommutativeMonoid record
      { Carrier = Vector Ann s
      ; _≤ε = _⊴* 0*
      ; _≤[_∙_] = λ R P Q → R ⊴* P +* Q
      ; isSkewCommutativeRelMonoid = {!!}
      }

  private
    variable
      PΓ QΔ RΘ : Ctx
      T U : Ctx → Set
      𝓥 𝓦 : Scoped
      A : Ty
      r : Ann

  record Ren (PΓ QΔ : Ctx) : Set where
    private
      s = PΓ .Ctx.s ; P = PΓ .Ctx.R ; Γ = PΓ .Ctx.Γ
      t = QΔ .Ctx.s ; Q = QΔ .Ctx.R ; Δ = QΔ .Ctx.Γ
    field
      act : Var A Γ → Var A Δ
      use-pres : Q ⊴* unrow (row P *ᴹ λ i j → 1ᴹ (act (var i refl) .idx) j)
  open Ren public

  private
    variable
      s t u : LTree
      Γ Δ Θ : Vector Ty _
      P Q R : Vector Ann _

  fromRen : let PΓ = ctx {s} P Γ; QΔ = ctx {t} Q Δ in
            Ren PΓ QΔ → Thinningᵣ PΓ QΔ
  fromRen {[-]} r =
    let v = r .act (var here refl) in
    ⟨_⟩·_ {z = 1ᴹ (v .idx)} (r .use-pres) (lvar (v .idx) (v .tyq) ⊴*-refl)
  fromRen {ε} r = ✴1⟨ r .use-pres ⟩
  fromRen {sl <+> sr} {P} {Γ} {t} {Q} {Δ} r =
    _✴⟨_⟩_ {y = {!!}} {{!!}} (fromRen {sl} rl) {!!} {!!}
    where
    rl : Ren (ctx (P ∘ ↙) (Γ ∘ ↙)) (ctx {!!} _)
    rl .act (var i q) = r .act (var (↙ i) q)
    rl .use-pres = {!!}  -- ⊴*-trans (r .use-pres) (mk λ j → {!!})

  re^Th : let PΓ = ctx {s} P Γ in
          Thinningᵣ PΓ QΔ → Thinningᵣ PΓ (QΔ ++ᶜ ctx {u} 0* Θ)
  re^Th {[-]} θ = {!!}
  re^Th {ε} θ = {!!}
  re^Th {s <+> t} θ = {!!}

  identity : let PΓ = ctx {s} P Γ in Thinningᵣ PΓ PΓ
  identity {[-]} =
    ⟨_⟩·_ {z = λ _ → 1#} [ *.identity .proj₂ _ ]₂ (lvar here refl [ ⊴-refl ]₂)
  identity {ε} = ✴1⟨ []₂ ⟩
  identity {s <+> t} {P} {Γ} =
    _✴⟨_⟩_ {y = P ∘ ↙ ++ 0*} {0* ++ P ∘ ↘}
      {!!}
      ((mk λ _ → +.identity-→ .proj₂ _) ++₂ (mk λ _ → +.identity-← .proj₁ _))
      {!!}

  module _ (psh^𝓥 : IsPresheaf 𝓥) where

    select :
      let PΓ = ctx {s} P Γ; QΔ = ctx {t} Q Δ in
      Thinningᵣ PΓ QΔ → ∀[ (QΔ ─Envᵣ) 𝓥 ⇒ (PΓ ─Envᵣ) 𝓥 ]
    select {s = s} {t = [-]} th ρ = {!!}
    select {s = s} {t = ε} th ρ = {!!}
    select {s = s} {t = tl <+> tr} th (σ ✴⟨ sp ⟩ τ) =
      let foo = select {s = s} {t = tl} {!th!} σ in
      {!!}
    -- select {s = [-]} {t = t} th ρ = {!!}
    -- select {s = ε} {t = t} th ρ = {!!}
    -- select {s = sl <+> sr} {t = t} (thl ✴⟨ sp ⟩ thr) ρ =
    --   {!select {sl} thl ?!}
