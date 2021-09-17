{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Po
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel)

module Generic.Linear.Variable
  (Ty : Set) (rawPoSemiring : RawPoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open RawPoSemiring rawPoSemiring renaming (Carrier to Ann)

  open import Relation.Binary.PropositionalEquality

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Relation.Nary
  open import Relation.Unary.Bunched.Checked

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring

  infix 20 _∋_

  record _∋_ (Γ : Ctx) (A : Ty) : Set where
    constructor lvar

    open Ctx Γ renaming (shape to s; ty-ctx to γ; use-ctx to P)

    field
      idx : Ptr s
      tyq : γ idx ≡ A
      basis : P ≤* ⟨ idx ∣
  open _∋_ public

  infix 6 _↙ᵛ_ _↘ᵛ_

  hereᵛ : ∀ {sΓ : SizedCtx [-]} {A} → let Γ@(ctx P γ) = sctx→ctx sΓ in
    γ here ≡ A → P here ≤ 1# → Γ ∋ A
  hereᵛ q le .idx = here
  hereᵛ q le .tyq = q
  hereᵛ q le .basis = [ le ]ₙ

  _↙ᵛ_ : ∀ {s t} {sΓ : SizedCtx (s <+> t)} {A} → let Γ = sctx→ctx sΓ in
    leftᶜ Γ ∋ A → rightᶜ Γ .use-ctx ≤0* → Γ ∋ A
  (v ↙ᵛ _) .idx = ↙ (v .idx)
  (v ↙ᵛ _) .tyq = v .tyq
  (v ↙ᵛ sp0) .basis = v .basis ++ₙ 0*→≤* sp0

  _↘ᵛ_ : ∀ {s t} {sΓ : SizedCtx (s <+> t)} {A} → let Γ = sctx→ctx sΓ in
    leftᶜ Γ .use-ctx ≤0* → rightᶜ Γ ∋ A → Γ ∋ A
  (_ ↘ᵛ v) .idx = ↘ (v .idx)
  (_ ↘ᵛ v) .tyq = v .tyq
  (sp0 ↘ᵛ v) .basis = 0*→≤* sp0 ++ₙ v .basis
