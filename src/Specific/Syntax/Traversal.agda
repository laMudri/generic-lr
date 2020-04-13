{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra using (Op₂)
import Algebra.Definitions as Defs
open import Function.Base
open import Level using (0ℓ)
open import Relation.Binary using (Rel; Reflexive; Transitive)

module Specific.Syntax.Traversal
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
  open import Specific.Syntax.Prelude Ann _⊴_ 0# _+_ 1# _*_
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
      T : Ctx → Ty → Set

  record Env (T : Ctx → Ty → Set) (PΓ QΔ : Ctx) : Set where
    private
      s = PΓ .shape ; P = PΓ .use-ctx ; Γ = PΓ .ty-ctx
      t = QΔ .shape ; Q = QΔ .use-ctx ; Δ = QΔ .ty-ctx
    field
      matrix : Matrix Ann t s
      act : (j : Ptr t) → T (record PΓ { R = matrix j }) (Δ j)
      use-pres : P ⊴* unrow (row Q *ᴹ matrix)
  open Env public

  private
    variable
      s t : LTree
      P Q : Vector Ann s
      Γ : Vector Ty s
      Θ : Vector Ty t

  record Kit (T : Ctx → Ty → Set) : Set where
    field
      psh : P ⊴* Q → T (ctx Q Γ) A → T (ctx P Γ) A
      vr : LVar PΓ A → T PΓ A
      tm : T PΓ A → Tm PΓ A
      wk : T PΓ A → T (PΓ ++ᶜ ctx 0* Θ) A
  open Kit public

  module _ (K : Kit T) where

    bindEnv : Env T PΓ QΔ → Env T (PΓ ++ᶜ RΘ) (QΔ ++ᶜ RΘ)
    bindEnv τ .matrix = [ [ τ .matrix │ lift₀ᴹ 0# ]
                                       ─
                           [ lift₀ᴹ 0# │        1ᴹ ] ]
    bindEnv τ .act (↙ j) = K .wk (τ .act j)
    bindEnv τ .act (↘ j) = K .vr (lvar (↘ j) (⊴*-refl ++₂ ⊴*-refl) refl)
    bindEnv {QΔ = ctx Q Δ} {RΘ = ctx R Θ} τ .use-pres =
      ⊴*-trans (mk λ i → +-identity-⊵ .proj₂ _)
               (+*-mono (τ .use-pres) (unrowL₂ (*ᴹ-0ᴹ (row R))))
      ++₂
      ⊴*-trans (mk λ i → +-identity-⊵ .proj₁ _)
               (+*-mono (unrowL₂ (*ᴹ-0ᴹ (row Q))) (unrowL₂ (*ᴹ-1ᴹ (row R))))

    trav : Env T PΓ QΔ → Tm QΔ A → Tm PΓ A
    trav τ (var (lvar i sp refl)) = K .tm
      (K .psh
        (⊴*-trans (τ .use-pres)
                  (⊴*-trans (unrowL₂ (*ᴹ-mono (rowL₂ sp) ⊴ᴹ-refl))
                            (getrowL₂ (1ᴹ-*ᴹ (τ .matrix)) i)))
        (τ .act i))
    trav τ (app M N sp) =
      app (trav (record { Env τ; use-pres = ⊴*-refl }) M)
          (trav (record { Env τ; use-pres = ⊴*-refl }) N)
          (⊴*-trans (τ .use-pres)
                    (unrowL₂
                      (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp) ⊴ᴹ-refl)
                                (+ᴹ-*ᴹ _ _ (τ .matrix)))))
    trav τ (lam M) = lam (trav (bindEnv τ) M)
    trav τ (unm M N sp) =
      unm (trav (record { Env τ; use-pres = ⊴*-refl }) M)
          (trav (record { Env τ; use-pres = ⊴*-refl }) N)
          (⊴*-trans (τ .use-pres)
                    (unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp) ⊴ᴹ-refl)
                                       (+ᴹ-*ᴹ _ _ (τ .matrix)))))
    trav τ (uni sp) =
      uni (⊴*-trans (τ .use-pres)
                    (unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp) ⊴ᴹ-refl)
                                       (0ᴹ-*ᴹ (τ .matrix)))))
    trav τ (prm M N sp) =
      prm (trav (record { Env τ; use-pres = ⊴*-refl }) M)
          (trav (bindEnv record { Env τ; use-pres = ⊴*-refl }) N)
          (⊴*-trans (τ .use-pres)
                    (unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp) ⊴ᴹ-refl)
                                       (+ᴹ-*ᴹ _ _ (τ .matrix)))))
    trav τ (ten M N sp) =
      ten (trav (record { Env τ; use-pres = ⊴*-refl }) M)
          (trav (record { Env τ; use-pres = ⊴*-refl }) N)
          (⊴*-trans (τ .use-pres)
                    (unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp) ⊴ᴹ-refl)
                                       (+ᴹ-*ᴹ _ _ (τ .matrix)))))
    trav τ (exf M sp) =
      exf (trav (record { Env τ; use-pres = ⊴*-refl }) M)
          (⊴*-trans (τ .use-pres)
                    (unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp) ⊴ᴹ-refl)
                                       (+ᴹ-*ᴹ _ _ (τ .matrix)))))
    trav τ (cse M N O sp) =
      cse (trav (record { Env τ; use-pres = ⊴*-refl }) M)
          (trav (bindEnv record { Env τ; use-pres = ⊴*-refl }) N)
          (trav (bindEnv record { Env τ; use-pres = ⊴*-refl }) O)
          (⊴*-trans (τ .use-pres)
                    (unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp) ⊴ᴹ-refl)
                                       (+ᴹ-*ᴹ _ _ (τ .matrix)))))
    trav τ (inl M) = inl (trav τ M)
    trav τ (inr M) = inr (trav τ M)
    trav τ top = top
    trav τ (prl M) = prl (trav τ M)
    trav τ (prr M) = prr (trav τ M)
    trav τ (wth M N) = wth (trav τ M) (trav τ N)
    trav τ (bam M N sp) =
      bam (trav (record { Env τ; use-pres = ⊴*-refl }) M)
          (trav (bindEnv record { Env τ; use-pres = ⊴*-refl }) N)
          (⊴*-trans (τ .use-pres)
                    (unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp) ⊴ᴹ-refl)
                                       (+ᴹ-*ᴹ _ _ (τ .matrix)))))
    trav τ (bng M sp) =
      bng (trav (record { Env τ; use-pres = ⊴*-refl }) M)
          (⊴*-trans (τ .use-pres)
                    (unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp) ⊴ᴹ-refl)
                                       (*ₗ-*ᴹ _ _ (τ .matrix)))))
