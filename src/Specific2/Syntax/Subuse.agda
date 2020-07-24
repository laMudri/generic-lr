{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ)

module Specific2.Syntax.Subuse (algebra : SkewSemiring 0ℓ 0ℓ) where

  open import Specific2.Syntax.Prelude algebra

  open import Specific2.Syntax Ann _⊴_ 0# _+_ 1# _*_
  open import Specific2.Syntax.Renaming.IdHom algebra
  open import Generic.Linear.Syntax Ty Ann

  open import Data.LTree
  open import Data.LTree.Vector using (Vector)
  open import Data.LTree.Matrix using (unrowL₂)
  open import Function.Base

  private
    variable
      A : Ty
      s : LTree
      P Q : Vector Ann s
      Γ : Vector Ty s

  subuse : P ⊴* Q → Tm (ctx Q Γ) A → Tm (ctx P Γ) A
  subuse PQ = ren′ record
    { act = id
    ; use-pres = ⊴*-trans PQ (unrowL₂ (*ᴹ-1ᴹ _))
    }
