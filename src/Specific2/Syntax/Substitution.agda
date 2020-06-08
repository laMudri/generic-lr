{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ)

module Specific2.Syntax.Substitution (algebra : SkewSemiring 0ℓ 0ℓ) where

  open import Specific2.Syntax.Prelude algebra

  open import Specific2.Syntax Ann _⊴_ 0# _+_ 1# _*_
  open import Specific2.Syntax.Traversal algebra
  open import Specific2.Syntax.Renaming algebra
  open import Specific2.Syntax.Subuse algebra
  open import Generic.Linear.Syntax Ty Ann

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.Product
  open import Function.Base
  open import Relation.Binary.PropositionalEquality

  private
    variable
      A B C : Ty
      PΓ QΔ RΘ : Ctx

  Sub = DeployedEnv Tm

  private
    variable
      t : LTree
      Θ : Vector Ty t

  weakenRen : Ren (PΓ ++ᶜ ctx (λ _ → 0#) Θ) PΓ
  weakenRen .act (ivar i q) = ivar (↙ i) q
  weakenRen {PΓ = ctx P Γ} .use-pres =
    unrowL₂ (*ᴹ-1ᴹ _) ++₂ unrowL₂ (*ᴹ-0ᴹ (row P))

  Tm-kit : Kit Tm
  Tm-kit = record { psh = subuse ; vr = var ; tm = id ; wk = ren weakenRen }

  sub : Sub PΓ QΔ → Tm QΔ A → Tm PΓ A
  sub σ = travD Tm-kit σ
