{-# OPTIONS --safe --sized-types --without-K --postfix-projections #-}

open import Algebra.Core
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel; IsPreorder; Reflexive; Transitive)

module Generic.Linear.Sec3
  (Ann : Set) (_⊴_ : Rel Ann 0ℓ)
  (0# : Ann) (_+_ : Op₂ Ann) (1# : Ann) (_*_ : Op₂ Ann)
  -- (let module ⊴ = Defs _⊴_)
  -- (let module ⊵ = Defs (flip _⊴_))
  -- (open ⊴ using (Congruent₂; Interchangable))
  -- ⊴:
  (⊴-refl : Reflexive _⊴_)
  (⊴-trans : Transitive _⊴_)
  where

  open import Data.LTree
  open import Data.LTree.Vector
  0* = lift₀ 0#
  open import Data.LTree.Matrix
  open import Data.LTree.Matrix.Properties
  open import Data.Product
  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary

  open Mult 0# _+_ _*_
  open Reflᴹ _⊴_ ⊴-refl renaming (reflᴹ to ⊴ᴹ-refl)
  open Transᴹ _⊴_ ⊴-trans renaming (transᴹ to ⊴ᴹ-trans)
  open Plus-cong _+_ _⊴_ _⊴_ _⊴_ {!!}
    renaming (+ᴹ-cong to +ᴹ-mono)
  open Mult-cong 0# _+_ _*_ _⊴_ _⊴_ _⊴_ {!!} {!!} {!!}
    renaming (*ᴹ-cong to *ᴹ-mono)
  -- open MultIdent 0# 1# _⊴_ 0# _+_ _*_ {!!} {!!} {!!} {!!} {!!} {!!}
  open IdentMult 0# 1# _⊴_ 0# _+_ _*_ {!!} {!!} {!!} {!!} {!!} {!!}
  open MultMult _⊴_ 0# _+_ 0# _+_ 0# _+_ _*_ _*_ _*_ _*_ ⊴-refl ⊴-trans
    {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}
  open PlusMult _+_ _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans {!⊴-mono!} {!!} {!!} {!!}
  open LeftScaleMult _⊴_ 0# _+_ 0# _+_ _*_ _*_ _*_ _*_ ⊴-refl ⊴-trans
    {!!} {!!} {!!} {!!}

  data Ty : Set where
    ι : Ty
    _·_⊸_ : (r : Ann) (A B : Ty) → Ty

  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty Ann _⊴_ 0# _+_ 1# _*_
  open import Generic.Linear.Environment Ty Ann _⊴_ 0# _+_ 1# _*_
    renaming (var to mkVar)
  open import Generic.Linear.Thinning Ty Ann _⊴_ 0# _+_ 1# _*_
  open _─Env
  open import Generic.Linear.Thinning.Properties Ty Ann _⊴_ 0# _+_ 1# _*_
    {!!}  -- ⊴-refl
    {!!}  -- ⊴-trans
    {!!}  -- +-mono
    {!!}  -- +-identity-→
    {!!}  -- +-identity-←
    {!!}  -- +-interchange
    {!!}  -- *-mono
    {!!}  -- *-identityˡ-→
    {!!}  -- *-identityʳ-←
    {!!}  -- *-assoc-→
    {!!}  -- zeroˡ-→
    {!!}  -- distribˡ-→
    {!!}  -- zeroʳ-←
    {!!}  -- distribʳ-←
  open import Generic.Linear.Environment.Properties
    Ty Ann _⊴_ 0# _+_ 1# _*_ ⊴-refl ⊴-trans
    {!!} {!!}
    {!!} {!!}
    {!!}
    {!!} {!!} {!!}
    {!!} {!!}
    {!!}
    {!!}

  private
    variable
      A B : Ty
      r s : Ann
      RΓ PΓ QΔ RΘ : Ctx
      𝓥 𝓒 : Scoped

  data Tm : Scoped where
    `var : ∀[ LVar A ⇒ Tm A ]
    `app : ∀[ Tm (r · A ⊸ B) ✴ r · Tm A ⇒ Tm B ]
    `lam : ∀[ (_++ᶜ [ r · A ]ᶜ) ⊢ Tm B ⇒ Tm (r · A ⊸ B) ]

  -- TODO: This is basic. Move to Generic.Linear.Thinning or somewhere.
  llookup : IsPresheaf 𝓥 → (PΓ ─Env) 𝓥 QΔ → ∀ {A} → LVar A PΓ → 𝓥 A QΔ
  llookup 𝓥-psh ρ v = 𝓥-psh
    (⊴*-trans (ρ .sums)
              (⊴*-trans (unrowL₂ (*ᴹ-mono (rowL₂ (v .basis)) ⊴ᴹ-refl))
                        (getrowL₂ (1ᴹ-*ᴹ (ρ .M)) (v .idx))))
    (ρ .lookup (plain-var v))

  record Semantics (𝓥 𝓒 : Scoped) (𝓥-psh : IsPresheaf 𝓥)
                   : Set where
    field
      th^𝓥 : Thinnable (𝓥 A)
      var : ∀[ 𝓥 A ⇒ 𝓒 A ]
      app : ∀[ 𝓒 (r · A ⊸ B) ✴ r · 𝓒 A ⇒ 𝓒 B ]
      lam : ∀[ □ (r · 𝓥 A ─✴ 𝓒 B) ⇒ 𝓒 (r · A ⊸ B) ]

    _─Comp : Ctx → Scoped → Ctx → Set
    (PΓ ─Comp) 𝓒 QΔ = ∀ {A} → Tm A PΓ → 𝓒 A QΔ

    bind : (PΓ ─Env) 𝓥 QΔ →
           ∀[ Thinning QΔ ✴ (r · 𝓥 A) ⇒
           ((PΓ ++ᶜ [ r · A ]ᶜ) ─Env) 𝓥 ]
    bind {PΓ = PΓ} {QΔ = QΔ} ρ {RΘ} (_✴⟨_⟩_ {P = Rl} {Q = Rr} θ sp+ rv) =
      ++ᵉ (lemma ✴⟨ sp+ ⟩ [-]ᵉ rv)
      where
      lemma : (PΓ ─Env) 𝓥 record RΘ { R = Rl }
      lemma .M = ρ .M *ᴹ θ .M
      lemma .sums =
        ⊴*-trans (θ .sums)
                 (unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ (ρ .sums)) ⊴ᴹ-refl)
                                    (*ᴹ-*ᴹ-→ _ (ρ .M) (θ .M))))
                                    -- thinning-sub-1ᴹ θ ?
      lemma .lookup v@(mkVar i q) =
        th^𝓥 (ρ .lookup v) {!θ .sums!}

    semantics : (PΓ ─Env) 𝓥 QΔ → (PΓ ─Comp) 𝓒 QΔ
    semantics ρ (`var x) = var (llookup 𝓥-psh ρ x)
    semantics ρ (`app (M ✴⟨ sp+ ⟩ (⟨ sp· ⟩· N))) =
      app (semantics (record { _─Env ρ; sums = ⊴*-refl }) M
           ✴⟨ ⊴*-trans (ρ .sums)
              (unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp+) ⊴ᴹ-refl)
                                 (+ᴹ-*ᴹ _ _ (_─Env.M ρ)))) ⟩
           (⟨ unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp·) ⊴ᴹ-refl)
                                (*ₗ-*ᴹ _ _ (_─Env.M ρ))) ⟩·
            semantics (record { _─Env ρ; sums = ⊴*-refl }) N))
    semantics ρ (`lam M) = lam λ where
      θ .app✴ sp v → semantics (bind ρ (θ ✴⟨ sp ⟩ v)) M
