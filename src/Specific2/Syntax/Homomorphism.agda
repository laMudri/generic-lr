{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ)

module Specific2.Syntax.Homomorphism
  {Dom Cod : SkewSemiring 0ℓ 0ℓ} (f : SkewSemiringMor Dom Cod) where

  private
    open module f = SkewSemiringMor f
  import Specific2.Syntax.Prelude as Pre
  open import Specific2.Syntax as Syn
    using ( ivar; ivar!; lvar; lvar!; var; shape; use-ctx; ty-ctx
          ; idx; ty-eq; basis)
  open import Generic.Linear.Syntax as Gen using (ctx)

  open import Specific2.Syntax.Traversal f
  open import Specific2.Syntax.Renaming f

  open import Algebra.Skew.Construct.Vector
  open import Data.LTree
  open import Data.LTree.Vector using (Vector; mk; get)
  open import Data.LTree.Matrix using (Matrix; mk; get)
  open import Relation.Binary.PropositionalEquality

  private
    module Dom where
      open Pre Dom public
      open Syn Ann _⊴_ 0# _+_ 1# _*_ public hiding (ivar)
      open Gen Ty Ann public hiding (ctx; ctx→sctx)

    module Cod where
      open Pre Cod public
      open Syn Ann _⊴_ 0# _+_ 1# _*_ public hiding (ivar)
      open Gen Ty Ann public hiding (ctx; ctx→sctx)

  hom-tm : ∀ {RΓ A} → Dom.Tm RΓ A → Cod.Tm (hom RΓ) (hom A)
  hom-tm {ctx R Γ} = ren record
    { act = λ (ivar i q) → ivar i (cong hom q)
    ; use-pres = mk λ i → *ᴹ-1ᴹ (λ _ j → apply (R j)) .get here i
    } where open Cod
