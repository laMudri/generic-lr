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
  open import Function.Base using (_∘_)

  private
    variable
      PΓ QΔ RΘ : Ctx
      T : Ctx → Set
      𝓥 : Scoped

  -- TODO: this probably should be somewhere else.
  IsPresheaf : Scoped → Set
  IsPresheaf 𝓒 =
    ∀ {RΓ : Ctx} {A P Q} → let ctx R Γ = RΓ in
    Q ⊴* P → 𝓒 A (ctx P Γ) → 𝓒 A (ctx Q Γ)

  record Var {s} (A : Ty) (Γ : Vector Ty s) : Set where
    constructor var
    field
      idx : Ptr s
      tyq : Γ idx ≡ A
  open Var public

  record _─Env (PΓ : Ctx) (𝓥 : Scoped) (QΔ : Ctx) : Set where
    constructor pack

    open Ctx PΓ renaming (s to s; Γ to Γ; R to P)
    open Ctx QΔ renaming (s to t; Γ to Δ; R to Q)

    field
      M : Matrix Ann s t
      sums : Q ⊴* unrow (mult 0# _+_ _*_ (row P) M)
      lookup : ∀ {A} (v : Var A Γ) → 𝓥 A (record QΔ { R = M (Var.idx v) })
  open _─Env  -- TODO: better names so this can be public

  leftᵛ : ∀ {s t A} {Γ : Vector Ty (s <+> t)} → Var A (Γ ∘ ↙) → Var A Γ
  leftᵛ (var i q) = var (↙ i) q
  rightᵛ : ∀ {s t A} {Γ : Vector Ty (s <+> t)} → Var A (Γ ∘ ↘) → Var A Γ
  rightᵛ (var i q) = var (↘ i) q
