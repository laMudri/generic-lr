{-# OPTIONS --safe --without-K #-}

open import Algebra.Core
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel)

module Generic.Linear.Thinning
  (Ty Ann : Set) (_⊴_ : Rel Ann 0ℓ)
  (0# : Ann) (_+_ : Op₂ Ann) (1# : Ann) (_*_ : Op₂ Ann)
  where

  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open Ident 0# 1#

  open import Generic.Linear.Operations _⊴_ 0# _+_ 1# _*_
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Environment Ty Ann _⊴_ 0# _+_ 1# _*_

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
