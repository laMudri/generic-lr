{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Core
import Algebra.Definitions as Defs
open import Function.Base using (flip; _∘_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel; IsPreorder; Reflexive; Transitive)

module Generic.Linear.Environment.Properties
  (Ty Ann : Set) (_⊴_ : Rel Ann 0ℓ)
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

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.LTree.Matrix.Properties
  open import Data.Product
  open import Relation.Unary
  open import Relation.Binary.PropositionalEquality

  -- open Mult 0# _+_ _*_
  open MultMult _⊴_ 0# _+_ 0# _+_ 0# _+_ _*_ _*_ _*_ _*_ ⊴-refl ⊴-trans
    +-mono (+-identity-⊴ .proj₁ 0#) (+-identity-⊵ .proj₂ 0#) +-interchange
    *-* 0-* (λ z x y → +-* x y z) *-0 *-+

  open import Generic.Linear.Operations _⊴_ 0# _+_ 1# _*_
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty Ann _⊴_ 0# _+_ 1# _*_
  open import Generic.Linear.Environment Ty Ann _⊴_ 0# _+_ 1# _*_
  open _─Env
  open import Generic.Linear.Thinning Ty Ann _⊴_ 0# _+_ 1# _*_
  open import Specific.Syntax.Prelude Ann _⊴_ 0# _+_ 1# _*_
    ⊴-refl ⊴-trans +-mono *-mono +-identity-⊴ +-identity-⊵ +-interchange
    1-* *-1 *-* 0-* *-0 +-* *-+

  private
    variable
      PΓ QΔ RΘ : Ctx
      T : Ctx → Set
      𝓥 𝓦 : Scoped
      s t u : LTree
      P Q R : Vector Ann s
      A : Ty
      r : Ann

  th^Env : (∀ {A} → Thinnable (𝓥 A)) → Thinnable ((PΓ ─Env) 𝓥)
  th^Env th^𝓥 ρ ren .M = ρ .M *ᴹ ren .M
  th^Env th^𝓥 ρ ren .sums =
    ⊴*-trans (ren .sums)
             (⊴*-trans (unrowL₂ (*ᴹ-mono (rowL₂ (ρ .sums)) ⊴ᴹ-refl))
                       (unrowL₂ (*ᴹ-*ᴹ-→ _ (ρ .M) (ren .M))))
  th^Env th^𝓥 {QΔ} ρ {RΘ} ren .lookup v =
    th^𝓥 (ρ .lookup v) record { _─Env ren; sums = ⊴*-refl }

  []ᵉ : ∀[ ✴1 ⇒ ([]ᶜ ─Env) 𝓥 ]
  []ᵉ ✴1⟨ sp ⟩ .M = [─]
  []ᵉ ✴1⟨ sp ⟩ .sums = sp
  []ᵉ ✴1⟨ sp ⟩ .lookup (var (there () _) _)

  ++ᵉ : ∀[ (PΓ ─Env) 𝓥 ✴ (QΔ ─Env) 𝓥 ⇒ ((PΓ ++ᶜ QΔ) ─Env) 𝓥 ]
  ++ᵉ (ρ ✴⟨ sp ⟩ σ) .M = [ ρ .M
                             ─
                           σ .M ]
  ++ᵉ (ρ ✴⟨ sp ⟩ σ) .sums = ⊴*-trans sp (+*-mono (ρ .sums) (σ .sums))
  ++ᵉ (ρ ✴⟨ sp ⟩ σ) .lookup (var (↙ i) q) = ρ .lookup (var i q)
  ++ᵉ (ρ ✴⟨ sp ⟩ σ) .lookup (var (↘ i) q) = σ .lookup (var i q)

  [-]ᵉ : ∀[ r · 𝓥 A ⇒ ([ r · A ]ᶜ ─Env) 𝓥 ]
  [-]ᵉ (⟨ sp ⟩· v) .M = row _
  [-]ᵉ (⟨ sp ⟩· v) .sums = sp
  [-]ᵉ (⟨ sp ⟩· v) .lookup (var _ refl) = v

  -- _<$>_ : ((∀ {A} → 𝓥 A record QΔ { R = N i } → 𝓦 A RΘ) ×
  --          ∃ \ N → Ctx.R RΘ ⊴* unrow (row (Ctx.R QΔ) *ᴹ N)) →
  --         (PΓ ─Env) 𝓥 QΔ → (PΓ ─Env) 𝓦 RΘ
  -- ((f , N , sp) <$> ρ) .M = ρ .M *ᴹ N
  -- ((f , N , sp) <$> ρ) .sums =
  --   ⊴*-trans sp (unrowL₂
  --   (⊴ᴹ-trans (*ᴹ-mono (rowL₂ (ρ .sums)) ⊴ᴹ-refl)
  --             (*ᴹ-*ᴹ-→ _ (ρ .M) N)))
  -- ((f , N , sp) <$> ρ) .lookup v =
  --   {!(ρ .lookup v)!}
