{-# OPTIONS --safe --sized-types --without-K #-}

open import Algebra.Core
open import Algebra.Skew
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel; IsPreorder; Reflexive; Transitive)

module Generic.Linear.Semantics
  (Ty : Set) (skewSemiring : SkewSemiring lzero lzero)
  where

  open SkewSemiring skewSemiring
    renaming (Carrier to Ann
             ; _≤_ to _⊴_
             ; refl to ⊴-refl; trans to ⊴-trans
             )

  open import Data.LTree
  open import Data.LTree.Vector
  0* = lift₀ 0#
  open import Data.LTree.Matrix
  open import Data.LTree.Matrix.Properties
  open import Size
  open import Relation.Unary

  _⊴*_ = Lift₂ _⊴_
  open Reflᴹ _⊴_ ⊴-refl renaming (reflᴹ to ⊴ᴹ-refl)
  open Transᴹ _⊴_ ⊴-trans renaming (transᴹ to ⊴ᴹ-trans)
  open Mult 0# _+_ _*_
  open Mult-cong 0# _+_ _*_ _⊴_ _⊴_ _⊴_ {!!} {!!} {!!}
  -- open MultIdent 0# 1# _⊴_ 0# _+_ _*_ {!!} {!!} {!!} {!!} {!!} {!!}
  open IdentMult 0# 1# _⊴_ 0# _+_ _*_ {!!} {!!} {!!} {!!} {!!} {!!}

  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty Ann _⊴_ 0# _+_ 1# _*_
  open import Generic.Linear.Syntax.Interpretation.Map Ty {!!}
  open import Generic.Linear.Syntax.Term Ty Ann _⊴_ 0# _+_ 1# _*_
  open import Generic.Linear.Environment Ty Ann _⊴_ 0# _+_ 1# _*_ hiding (var)
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
      A : Ty

  Kripke : (𝓥 𝓒 : Scoped) (PΓ : Ctx) (A : Ty) → Ctx → Set
  Kripke 𝓥 𝓒 PΓ A = □ ((PΓ ─Env) 𝓥 ⇒ 𝓒 A)

  record Semantics (d : System) (𝓥 𝓒 : Scoped) (𝓥-psh : IsPresheaf 𝓥)
                   : Set where
    field
      th^𝓥 : Thinnable (𝓥 A)
      var : ∀[ 𝓥 A ⇒ 𝓒 A ]
      alg : ∀[ ⟦ d ⟧s (Kripke 𝓥 𝓒) A ⇒ 𝓒 A ]

    _─Comp : Ctx → Scoped → Ctx → Set
    (PΓ ─Comp) 𝓒 QΔ = ∀ {sz A} → Tm d sz A PΓ → 𝓒 A QΔ

    semantics : ∀ {PΓ QΔ} → (PΓ ─Env) 𝓥 QΔ → (PΓ ─Comp) 𝓒 QΔ
    body : ∀ {PΓ QΔ sz} → (PΓ ─Env) 𝓥 QΔ → ∀ {RΘ A} →
           Scope (Tm d sz) record RΘ { R = 0* } A PΓ → Kripke 𝓥 𝓒 RΘ A QΔ

    semantics ρ (`var v) =
      var (𝓥-psh (⊴*-trans (ρ .sums)
                           (⊴*-trans (unrowL₂ (*ᴹ-cong (rowL₂ (v .basis))
                                                       ⊴ᴹ-refl))
                                     (getrowL₂ (1ᴹ-*ᴹ (ρ .M)) (v .idx))))
                 (ρ .lookup (plain-var v)))
    semantics {ctx P Γ} {ctx Q Δ} ρ (`con {sz = sz} t) =
      alg (map-s {_} {_} {Γ} {Δ}
                 (record
                   { prosetRel = record
                     { rel = λ P Q → Q ⊴* unrow (row P *ᴹ ρ .M)
                     ; rel-mono = {!!}
                     }
                   ; rel-0ₘ = {!!}
                   ; rel-+ₘ = {!!}
                   ; rel-*ₘ = {!Kripke 𝓥 𝓒!} })
                 {X = Scope (Tm d sz)} {Kripke 𝓥 𝓒}
                 d
                 (λ {RΘ} {A} r x → body {ctx {!!} Γ} {ctx {!!} Δ} {sz = sz} {!ρ!} {{!!}} {A} x {!!})
                 {_} {P} {Q}
                 (ρ .sums)
                 t)
      -- alg (map-s d (body {sz = sz} {!ρ!}) {!t!})

    body ρ t {QΔ′} th σ = semantics (let foo = th^Env th^𝓥 ρ th in {!σ!}) t
