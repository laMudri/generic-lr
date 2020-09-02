{-# OPTIONS --safe --without-K #-}

open import Algebra.Skew
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel)

module Generic.Linear.Thinning
  (Ty : Set) (rawSkewSemiring : RawSkewSemiring 0ℓ 0ℓ)
  where

  open RawSkewSemiring rawSkewSemiring renaming (Carrier to Ann; _≤_ to _⊴_)

  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix

  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Environment Ty rawSkewSemiring

  record LVar (A : Ty) (PΓ : Ctx) : Set where
    constructor lvar

    open Ctx PΓ renaming (s to s; Γ to Γ; R to P)

    field
      idx : Ptr s
      tyq : Γ idx ≡ A
      basis : P ⊴* 1ᴹ idx
  open LVar public

  plain-var : ∀ {A PΓ} → LVar A PΓ → Var A (Ctx.Γ PΓ)
  idx (plain-var v) = idx v
  tyq (plain-var v) = tyq v

  Thinning : (PΓ QΔ : Ctx) → Set
  Thinning PΓ QΔ = (PΓ ─Env) LVar QΔ

  □ : (Ctx → Set) → (Ctx → Set)
  (□ T) PΓ = ∀[ Thinning PΓ ⇒ T ]

  Thinnable : (Ctx → Set) → Set
  Thinnable T = ∀[ T ⇒ □ T ]
