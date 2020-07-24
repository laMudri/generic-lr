{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ; _⊔_)

module Specific2.Syntax.Renaming.IdHom (algebra : SkewSemiring 0ℓ 0ℓ) where

  open import Specific2.Syntax.Prelude algebra
  open import Specific2.Syntax Ann _⊴_ 0# _+_ 1# _*_
  open import Algebra.Skew.Construct.Vector
  open import Specific2.Syntax.Traversal {algebra} id-SkewSemiringMor
  open import Specific2.Syntax.Traversal.IdHom algebra
  open import Generic.Linear.Syntax Ty Ann

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.Product
  open import Function.Base
  open import Relation.Binary.PropositionalEquality

  open import Specific2.Syntax.Renaming {algebra} id-SkewSemiringMor

  open Sum 0# _+_

  record Ren′ (PΓ : Ctx) (QΔ : Ctx) : Set where
    private
      s = PΓ .shape ; P = PΓ .use-ctx ; Γ = PΓ .ty-ctx
      t = QΔ .shape ; Q = QΔ .use-ctx ; Δ = QΔ .ty-ctx
    field
      act : ∀ {A} → IVar Δ A → IVar Γ A
      use-pres : P ⊴* λ i → ∑ λ j → Q j * ⟨ act (ivar! j) .idx ∣ i
  open Ren′ public

  Ren′⇒Ren : ∀ {PΓ QΔ} → Ren′ PΓ QΔ → Ren PΓ QΔ
  Ren′⇒Ren r .act w .idx = r .act w .idx
  Ren′⇒Ren r .act w .ty-eq = trans (r .act w .ty-eq) (sym hom-id)
  Ren′⇒Ren r .use-pres = r .use-pres

  module _ {PΓ QΔ} (let s = PΓ .shape) (let t = QΔ .shape)
                   (let Γ = PΓ .ty-ctx) (let Δ = QΔ .ty-ctx)
    where
    open SkewLeftSemimoduleMor
    open ProsetMor

    renMap′ : Ren′ PΓ QΔ → LinMap′ t s
    renMap′ r = renMap (Ren′⇒Ren r)

    renEnv′ : (r : Ren′ PΓ QΔ) → Env′ LVar (renMap′ r) Γ Δ
    renEnv′ r = Env⇒Env′ (renEnv (Ren′⇒Ren r))

  ren′ : ∀ {PΓ QΔ A} → Ren′ PΓ QΔ → Tm QΔ A → Tm PΓ A
  ren′ r = trav′ LVar-kit (renEnv′ r) (mk (r .use-pres))
