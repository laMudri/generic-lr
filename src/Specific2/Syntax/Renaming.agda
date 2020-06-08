{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ)

module Specific2.Syntax.Renaming (algebra : SkewSemiring 0ℓ 0ℓ) where

  open import Specific2.Syntax.Prelude algebra

  open import Specific2.Syntax Ann _⊴_ 0# _+_ 1# _*_
  open import Specific2.Syntax.Traversal algebra
  open import Generic.Linear.Syntax Ty Ann

  open import Data.LTree
  open import Data.LTree.Vector using (_++₂_)
  open import Data.LTree.Matrix using (unrow; row)
  open import Data.Product
  open import Function.Base
  open import Relation.Binary.PropositionalEquality

  private
    variable
      A B C : Ty
      PΓ QΔ RΘ : Ctx

  record Ren (PΓ QΔ : Ctx) : Set where
    private
      s = PΓ .shape ; P = PΓ .use-ctx ; Γ = PΓ .ty-ctx
      t = QΔ .shape ; Q = QΔ .use-ctx ; Δ = QΔ .ty-ctx
    field
      act : IVar Δ A → IVar Γ A
      use-pres : P ⊴* unrow (row Q *ᴹ λ j i → 1ᴹ (act (ivar! j) .idx) i)
  open Ren public

  module _ where
    open Kit

    LVar-kit : Kit LVar
    LVar-kit .psh PQ v = equip-var (iVar v) (⊴*-trans PQ (v .basis))
    LVar-kit .vr = id
    LVar-kit .tm = var
    LVar-kit .wk v .idx = ↙ (v .idx)
    LVar-kit .wk v .ty-eq = v .ty-eq
    LVar-kit .wk v .basis = v .basis ++₂ ⊴*-refl

  ren : Ren PΓ QΔ → Tm QΔ A → Tm PΓ A
  ren r = trav LVar-kit
    (λ { .act j@(ivar! _) → equip-var (r .act j) ⊴*-refl })
    (mk (r .use-pres))
