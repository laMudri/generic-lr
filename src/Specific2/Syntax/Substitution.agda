{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ)

module Specific2.Syntax.Substitution
  {Dom Cod : SkewSemiring 0ℓ 0ℓ} (f : SkewSemiringMor Dom Cod) where

  private
    open module f = SkewSemiringMor f
  import Specific2.Syntax.Prelude as Pre
  open import Specific2.Syntax as Syn
    using ( ivar; ivar!; lvar; lvar!; var; shape; use-ctx; ty-ctx
          ; idx; ty-eq; basis)
  open import Generic.Linear.Syntax as Gen using (ctx)

  open import Specific2.Syntax.Traversal f
  open import Specific2.Syntax.Renaming.IdHom Cod
  open import Specific2.Syntax.Subuse Cod

  open import Algebra.Skew.Construct.Vector
  open import Data.LTree
  open import Data.LTree.Vector using (Vector; mk; get; _++₂_; module Sum)
  open import Data.LTree.Vector.Properties
  open import Data.LTree.Matrix using (unrow; row; unrowL₂)
  open import Data.Product
  open import Function.Base
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
      open Sum 0# _+_ public
      open SumCong _⊴_ 0# _+_ ⊴-refl +-mono public renaming (∑-cong to ∑-mono)
      open Sum0 _⊴_ 0# _+_ ⊴-trans ⊴-refl +-mono (+.identity-→ .proj₁ 0#)
        public
      open Sum+ _⊴_ 0# _+_ ⊴-refl ⊴-trans
                +-mono (+.identity-← .proj₁ 0#) +.inter public
      open SumLinear 0# _+_ (flip _⊴_) 0# _+_ ⊴-refl (flip ⊴-trans) +-mono
        public

  Sub = DeployedEnv Cod.Tm

  private
    variable
      t : LTree
      Θ : Vector _ t

  module _ where
    open Cod

    weakenRen : ∀ {PΓ} → Ren′ (PΓ ++ᶜ ctx (λ _ → 0#) Θ) PΓ
    weakenRen .act (ivar i q) = ivar (↙ i) q
    weakenRen {PΓ = ctx P Γ} .use-pres =
      unrowL₂ (*ᴹ-1ᴹ _) ++₂ unrowL₂ (*ᴹ-0ᴹ (row P))

  Tm-kit : Kit Cod.Tm
  Tm-kit = record { psh = subuse ; vr = var ; tm = id ; wk = ren′ weakenRen }

  sub : ∀ {PΓ QΔ A} → Sub PΓ QΔ → Dom.Tm QΔ A → Cod.Tm PΓ (hom A)
  sub σ = travD Tm-kit σ
