{-# OPTIONS --safe --without-K #-}

open import Algebra.Core
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel)

module Generic.Linear.Environment
  (Ty Ann : Set) (_⊴_ : Rel Ann 0ℓ)
  (0# : Ann) (_+_ : Op₂ Ann) (1# : Ann) (_*_ : Op₂ Ann)
  where

  open import Relation.Binary.PropositionalEquality

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Generic.Linear.Syntax Ty Ann

  open import Generic.Linear.Operations _⊴_ 0# _+_ 1# _*_

  open import Data.Product

  private
    variable
      PΓ QΔ RΘ : Ctx
      T : Ctx → Set
      𝓥 : Scoped

  record Var {s} (A : Ty) (Γ : Vector Ty s) : Set where
    constructor var
    field
      idx : Ptr s
      tyq : Γ idx ≡ A

  record _─Env (PΓ : Ctx) (𝓥 : Scoped) (QΔ : Ctx) : Set where
    constructor pack

    open Ctx PΓ renaming (s to s; Γ to Γ; R to P)
    open Ctx QΔ renaming (s to t; Γ to Δ; R to Q)

    field
      M : Matrix Ann s t
      sums : Q ⊴* unrow (mult 0# _+_ _*_ (row P) M)
      lookup : ∀ {A} (v : Var A Γ) → 𝓥 A (record QΔ { R = M (Var.idx v) })
  open _─Env  -- TODO: better names so this can be public

  -- split-env : ∀ {s t} {QΔ : SizedCtx (s <+> t)} → (PΓ ─Env) 𝓥 (sctx→ctx QΔ) →
  --             (PΓ ─Env) 𝓥 (leftᶜ QΔ) × (PΓ ─Env) 𝓥 (rightᶜ QΔ)
  -- split-env ρ .proj₁ .M = leftᴹ (ρ .M)
  -- split-env ρ .proj₁ .sums .get k = ρ .sums .get (go-left k)
  -- split-env ρ .proj₁ .lookup v = {!ρ .lookup v!}
  -- split-env ρ .proj₂ = {!!}
