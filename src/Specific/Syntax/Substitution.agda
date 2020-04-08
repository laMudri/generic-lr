{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra using (Op₂)
import Algebra.Definitions as Defs
open import Function.Base
open import Level using (0ℓ)
open import Relation.Binary using (Rel; Reflexive; Transitive)

module Specific.Syntax.Substitution
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

  open import Specific.Syntax Ann _⊴_ 0# _+_ 1# _*_
  open import Specific.Syntax.Renaming Ann _⊴_ 0# _+_ 1# _*_
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

  open Ident 0# 1#
  open Mult 0# _+_ _*_
  open Mult-cong 0# _+_ _*_ _⊴_ _⊴_ _⊴_ ⊴-refl +-mono *-mono
    renaming (*ᴹ-cong to *ᴹ-mono)
  open Plus-cong _+_ _⊴_ _⊴_ _⊴_ +-mono renaming (+ᴹ-cong to +ᴹ-mono)
  open IdentMult 0# 1# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
    +-mono +-identity-⊴ 1-* 0-*
  open MultIdent 0# 1# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
    +-mono +-identity-⊵ *-1 *-0
  open PlusMult _+_ _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
    +-mono (+-identity-⊵ .proj₂ 0#) +-interchange +-*
  open MultZero 0# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
    +-mono (+-identity-⊵ .proj₂ 0#) *-0
  open LeftScaleMult _⊴_ 0# _+_ 0# _+_ _*_ _*_ _*_ _*_ ⊴-refl ⊴-trans
    +-mono *-0 *-+ *-*
  open Cong2 _⊴_ +-mono renaming (cong₂ to +*-mono)

  private
    variable
      A B C : Ty
      PΓ QΔ RΘ : Ctx

  record Sub (PΓ QΔ : Ctx) : Set where
    private
      s = PΓ .shape ; P = PΓ .use-ctx ; Γ = PΓ .ty-ctx
      t = QΔ .shape ; Q = QΔ .use-ctx ; Δ = QΔ .ty-ctx
    field
      matrix : Matrix Ann t s
      act : (j : Ptr t) → Tm (record PΓ { R = matrix j }) (Δ j)
      use-pres : P ⊴* unrow (row Q *ᴹ matrix)
  open Sub public

  private
    variable
      t : LTree
      Θ : Vector Ty t

  weakenRen : Ren (PΓ ++ᶜ ctx (λ _ → 0#) Θ) PΓ
  weakenRen .act = ↙
  weakenRen {PΓ = ctx P Γ} .use-pres =
    unrowL₂ (*ᴹ-1ᴹ _) ++₂ unrowL₂ (*ᴹ-0ᴹ (row P))
  weakenRen .ty-pres j = refl

  bindSub : Sub PΓ QΔ → Sub (PΓ ++ᶜ RΘ) (QΔ ++ᶜ RΘ)
  bindSub σ .matrix = [ [    σ .matrix │ (λ _ _ → 0#) ]
                                       ─
                        [ (λ _ _ → 0#) │          1ᴹ  ] ]
  bindSub σ .act (↙ j) = ren weakenRen (σ .act j)
  bindSub σ .act (↘ j) = var (↘ j) (⊴*-refl ++₂ ⊴*-refl) refl
  bindSub {QΔ = ctx Q Δ} {RΘ = ctx R Θ} σ .use-pres =
    -- Note: this clause is copied directly from bindRen
    ⊴*-trans (mk λ i → +-identity-⊵ .proj₂ _)
             (+*-mono (σ .use-pres) (unrowL₂ (*ᴹ-0ᴹ (row R))))
    ++₂
    ⊴*-trans (mk λ i → +-identity-⊵ .proj₁ _)
             (+*-mono (unrowL₂ (*ᴹ-0ᴹ (row Q))) (unrowL₂ (*ᴹ-1ᴹ (row R))))

  -- TODO: show that `Tm`s form a presheaf with respect to subusaging.
  sub : Sub PΓ QΔ → Tm QΔ A → Tm PΓ A
  sub σ (var i sp refl) = {!σ .act i!}
  sub {PΓ = ctx {s} Rs Γ} {ctx {t} Rt Δ} σ (app M N sp) =
    -- Note: this clause is copied directly from ren
    app (sub (record { Sub σ; use-pres = ⊴*-refl }) M)
        (sub (record { Sub σ; use-pres = ⊴*-refl }) N)
        (⊴*-trans (σ .use-pres)
                  (unrowL₂
                    (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp) ⊴ᴹ-refl)
                              (⊴ᴹ-trans
                                (+ᴹ-*ᴹ {t = t} _ _ _)
                                (+ᴹ-mono ⊴ᴹ-refl (*ₗ-*ᴹ {t = t} _ _ _))))))
  sub σ (lam M) = lam (sub (bindSub σ) M)
