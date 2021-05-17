{-# OPTIONS --safe --without-K #-}

open import Algebra.Po
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel)

module Generic.Linear.Environment
  (Ty : Set) (rawPoSemiring : RawPoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open RawPoSemiring rawPoSemiring renaming (Carrier to Ann; _≤_ to _⊴_)

  open import Relation.Binary.PropositionalEquality

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix

  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring

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

  record _─Env (PΓ : Ctx) (𝓥 : Scoped ℓ) (QΔ : Ctx) : Set ℓ where
    constructor pack

    open Ctx PΓ renaming (s to s; Γ to Γ; R to P)
    open Ctx QΔ renaming (s to t; Γ to Δ; R to Q)

    field
      M : Matrix Ann s t
      sums : Q ⊴* unrow (mult 0# _+_ _*_ (row P) M)
      lookup : ∀ {A P′} → LVar A (ctx P′ Γ) → 𝓥 A (ctx (unrow (row P′ *ᴹ M)) Δ)
  open _─Env  -- TODO: better names so this can be public
