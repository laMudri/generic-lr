{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra using (Op₂)
import Algebra.Definitions as Defs
open import Function.Base
open import Level using (0ℓ)
open import Relation.Binary using (Rel; Reflexive; Transitive)

module Specific2.Syntax.Substitution
  (Ann : Set) (_⊴_ : Rel Ann 0ℓ)
  (0# : Ann) (_+_ : Op₂ Ann) (1# : Ann) (_*_ : Op₂ Ann)
  (⊴-refl : Reflexive _⊴_) (⊴-trans : Transitive _⊴_)
  (open Defs _⊴_) (let module ⊵ = Defs (flip _⊴_))
  (+-mono : Congruent₂ _+_) (*-mono : Congruent₂ _*_)
  (+-identity-⊴ : Identity 0# _+_) (+-identity-⊵ : ⊵.Identity 0# _+_)
  (+-interchange : Interchangable _+_ _+_)
  (1-* : ∀ x → (1# * x) ⊴ x) (*-1 : ∀ x → x ⊴ (x * 1#)) (*-* : Associative _*_)
  (0-* : ∀ x → (0# * x) ⊴ 0#) (*-0 : ∀ x → 0# ⊴ (x * 0#))
  (+-* : ∀ x y z → ((x + y) * z) ⊴ ((x * z) + (y * z)))
  (*-+ : ∀ x y z → ((x * y) + (x * z)) ⊴ (x * (y + z)))
  where

  open import Specific2.Syntax Ann _⊴_ 0# _+_ 1# _*_
  open import Specific2.Syntax.Prelude Ann _⊴_ 0# _+_ 1# _*_
    ⊴-refl ⊴-trans +-mono *-mono +-identity-⊴ +-identity-⊵ +-interchange
    1-* *-1 *-* 0-* *-0 +-* *-+
  open import Specific2.Syntax.Traversal Ann _⊴_ 0# _+_ 1# _*_
    ⊴-refl ⊴-trans +-mono *-mono +-identity-⊴ +-identity-⊵ +-interchange
    1-* *-1 *-* 0-* *-0 +-* *-+
  open import Specific2.Syntax.Renaming Ann _⊴_ 0# _+_ 1# _*_
    ⊴-refl ⊴-trans +-mono *-mono +-identity-⊴ +-identity-⊵ +-interchange
    1-* *-1 *-* 0-* *-0 +-* *-+
  open import Specific2.Syntax.Subuse Ann _⊴_ 0# _+_ 1# _*_
    ⊴-refl ⊴-trans +-mono *-mono +-identity-⊴ +-identity-⊵ +-interchange
    1-* *-1 *-* 0-* *-0 +-* *-+
  open import Generic.Linear.Syntax Ty Ann

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Vector.Properties
  open import Data.LTree.Matrix
  open import Data.LTree.Matrix.Properties
  open import Data.Product
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
