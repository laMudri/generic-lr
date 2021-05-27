{-# OPTIONS --safe --without-K --prop #-}

open import Algebra.Skew
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel)

module Generic.Linear.Environment
  (Ty : Set) (rawSkewSemiring : RawSkewSemiring 0ℓ 0ℓ)
  where

  open RawSkewSemiring rawSkewSemiring renaming (Carrier to Ann; _≤_ to _⊴_)

  open import Relation.Binary.PropositionalEquality

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix

  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Operations rawSkewSemiring

  open import Data.Product
  open import Function.Base using (_∘_)

  private
    variable
      PΓ QΔ RΘ : Ctx
      T : Ctx → Set
      ℓ : Level
      𝓥 : Scoped ℓ

  -- TODO: this probably should be somewhere else.
  IsPresheaf : Scoped ℓ → Set ℓ
  IsPresheaf 𝓒 =
    ∀ {s} {Γ : Vector Ty s} {P Q} {A} →
    Q ⊴* P → 𝓒 A (ctx P Γ) → 𝓒 A (ctx Q Γ)

  record Var {s} (A : Ty) (Γ : Vector Ty s) : Set where
    constructor var
    field
      idx : Ptr s
      tyq : Γ idx ≡ A
  open Var public

  record _─Env (PΓ : Ctx) (𝓥 : Scoped ℓ) (QΔ : Ctx) : Set ℓ where
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
