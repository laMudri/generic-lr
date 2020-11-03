{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ)

module Generic.Linear.Environment.Recursive.Properties
  (Ty : Set) (skewSemiring : SkewSemiring 0ℓ 0ℓ)
  where

  open SkewSemiring skewSemiring
    renaming (Carrier to Ann; _≤_ to _⊴_; refl to ⊴-refl; trans to ⊴-trans)

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.Product
  open import Function.Base using (_∘_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Algebra skewSemiring
  open import Generic.Linear.Syntax Ty Ann hiding ([_]ᶜ)
  open import Generic.Linear.Syntax.Interpretation Ty rawSkewSemiring
  open import Generic.Linear.Extend Ty skewSemiring
  open import Generic.Linear.Environment Ty rawSkewSemiring
  open import Generic.Linear.Environment.Recursive Ty rawSkewSemiring
  open import Generic.Linear.Thinning.Recursive Ty rawSkewSemiring
  -- open import Generic.Linear.Environment.Properties Ty skewSemiring

  open import Relation.Unary.Bunched hiding (✴1⟨_⟩; _✴⟨_⟩_; ⟨_⟩·_; lam✴; app✴)
  private
    open module Dummy0 {s} = BunchedUnit (_⊴* 0* {s})
    open module Dummy+ {s} =
      BunchedConjunction (λ (R P Q : Vector _ s) → R ⊴* P +* Q)
    open module Dummy* {s} =
      BunchedScaling (λ (R : Vector _ s) r P → R ⊴* r *ₗ P)
  open import Relation.Unary.Bunched.Properties
  private
    open module DummyCommMon {s} = BunchedCommutativeMonoid record
      { Carrier = Vector Ann s
      ; _≤ε = _⊴* 0*
      ; _≤[_∙_] = λ R P Q → R ⊴* P +* Q
      ; isSkewCommutativeRelMonoid = {!!}
      }

  private
    variable
      PΓ QΔ RΘ : Ctx
      T U : Ctx → Set
      𝓥 𝓦 : Scoped
      s t u : LTree
      Γ Δ Θ : Vector Ty _
      P Q R : Vector Ann _
      A : Ty
      r : Ann

  module _ where
    open _─Env

    toEnv : let PΓ = ctx {s} P Γ in (PΓ ─Envᵣ) 𝓥 QΔ → (PΓ ─Env) 𝓥 QΔ
    toEnv {[-]} _ .M = row _
    toEnv {ε} _ .M = [─]
    toEnv {s <+> t} (ρ ✴⟨ sp ⟩ σ) .M = [ toEnv {s} ρ .M
                                                ─
                                         toEnv {t} σ .M ]
    toEnv {[-]} (⟨ sp ⟩· v) .sums = sp
    toEnv {ε} ✴1⟨ sp ⟩ .sums = sp
    toEnv {s <+> t} (ρ ✴⟨ sp ⟩ σ) .sums =
      ⊴*-trans sp (+*-mono (toEnv {s} ρ .sums) (toEnv {t} σ .sums))
    toEnv {[-]} (⟨ sp ⟩· v) .lookup (var here refl) = v
    toEnv {ε} _ .lookup (var (there () i) q)
    toEnv {s <+> t} (ρ ✴⟨ sp ⟩ σ) .lookup (var (↙ i) q) =
      toEnv {s} ρ .lookup (var i q)
    toEnv {s <+> t} (ρ ✴⟨ sp ⟩ σ) .lookup (var (↘ i) q) =
      toEnv {t} σ .lookup (var i q)

    fromEnv : let PΓ = ctx {s} P Γ in (PΓ ─Env) 𝓥 QΔ → (PΓ ─Envᵣ) 𝓥 QΔ
    fromEnv {[-]} ρ = ⟨ ρ .sums ⟩· ρ .lookup (var here refl)
    fromEnv {ε} ρ = ✴1⟨ ρ .sums ⟩
    fromEnv {s <+> t} ρ = fromEnv {s} σ ✴⟨ ρ .sums ⟩ fromEnv {t} τ
      where
      σ : (ctx {s} _ _ ─Env) _ _
      σ .M = topᴹ (ρ .M)
      σ .sums = ⊴*-refl
      σ .lookup (var i q) = ρ .lookup (var (↙ i) q)

      τ : (ctx {t} _ _ ─Env) _ _
      τ .M = botᴹ (ρ .M)
      τ .sums = ⊴*-refl
      τ .lookup (var i q) = ρ .lookup (var (↘ i) q)

  Env-pres-✴1 : let PΓ = ctx {s} P Γ in
                (PΓ ─Envᵣ) 𝓥 QΔ → ✴1ᶜ PΓ → ✴1ᶜ QΔ
  Env-pres-✴1 {[-]} (⟨ sp* ⟩· _) ✴1⟨ sp0 ⟩ =
    ✴1⟨ ⊴*-trans sp* (mk λ i → ⊴-trans (*-mono (sp0 .get here) ⊴-refl)
                                       (annihil .proj₁ _)) ⟩
  Env-pres-✴1 {ε} ρ _ = ρ
  Env-pres-✴1 {sl <+> sr} (ρ ✴⟨ sp+ ⟩ σ) ✴1⟨ sp0 ⟩ =
    let ✴1⟨ sp0l ⟩ = Env-pres-✴1 ρ ✴1⟨ mk (sp0 .get ∘ ↙) ⟩ in
    let ✴1⟨ sp0r ⟩ = Env-pres-✴1 σ ✴1⟨ mk (sp0 .get ∘ ↘) ⟩ in
    ✴1⟨ ⊴*-trans sp+ (⊴*-trans (+*-mono sp0l sp0r) (mk λ i → +.identity-→ .proj₁ 0#)) ⟩

  Env-pres-✴ : let PΓ = ctx {s} P Γ in
               (PΓ ─Envᵣ) 𝓥 QΔ → (T ✴ᶜ U) PΓ → (T ✴ᶜ U) QΔ
  Env-pres-✴ {[-]} (⟨ sp* ⟩· v) (t ✴⟨ sp+ ⟩ u) = {!!} ✴⟨ {!sp+!} ⟩ {!!}
  Env-pres-✴ {ε} ✴1⟨ sp0 ⟩ tu =
    {!!}  -- {!Env-pres-✴ ? t!} ✴⟨ ⊴*-trans sp0 {!!} ⟩ {!!}
  Env-pres-✴ {sl <+> sr} ρ tu = {!map-✴ (Env-pres-✴ {sl} ? , Env-pres-✴ {sr} ?) tu!}

  th^Envᵣ : let PΓ = ctx {s} P Γ in
            (∀ {A} → Thinnableᵣ (𝓥 A)) → Thinnableᵣ ((PΓ ─Envᵣ) 𝓥)
  th^Envᵣ {[-]} th^𝓥 (⟨ sp ⟩· v) th = ⟨ {!toEnv sp ._─Env.sums!} ⟩· th^𝓥 v {!th!}
  th^Envᵣ {ε} th^𝓥 ρ th = Env-pres-✴1 th ρ
  th^Envᵣ {s <+> t} th^𝓥 ρ th = {!th!}
