{-# OPTIONS --safe --sized-types --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ)

module Generic.Linear.Semantics.Syntactic
  (Ty : Set) (skewSemiring : SkewSemiring 0ℓ 0ℓ)
  where

  open SkewSemiring skewSemiring
    renaming (Carrier to Ann
             ; _≤_ to _⊴_
             ; refl to ⊴-refl; trans to ⊴-trans
             )

  open import Algebra.Skew.Relation
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.Product
  open import Function.Base using (id; _∘_)
  open import Size
  open import Relation.Unary
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)

  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Algebra skewSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawSkewSemiring
  open import Generic.Linear.Syntax.Interpretation.Map Ty skewSemiring
  open import Generic.Linear.Syntax.Term Ty rawSkewSemiring
  open import Generic.Linear.Environment Ty rawSkewSemiring
    renaming (var to ivar)
  open import Generic.Linear.Thinning Ty rawSkewSemiring
  open _─Env
  open import Generic.Linear.Thinning.Properties Ty skewSemiring
  open import Generic.Linear.Environment.Properties Ty skewSemiring
  open import Generic.Linear.Semantics Ty skewSemiring

  private
    variable
      d : System
      A : Ty
      𝓥 𝓒 : Scoped
      RΘ : Ctx

  record VarLike (𝓥 : Scoped) : Set where
    constructor mk
    field get : ∀ {RΘ s Γ} → (RΘ ─Env) 𝓥 (ctx {s} 0* Γ ++ᶜ RΘ)
  open VarLike public

  open Semantics

  reify : VarLike 𝓥 → ∀[ Kripke 𝓥 𝓒 RΘ A ⇒ Scope 𝓒 RΘ A ]
  reify {RΘ = ctx R Θ} vl^𝓥 b =
    b (extend ⊴*-refl) .app✴ (+*-identity↘ _ ++₂ +*-identity↙ _) (vl^𝓥 .get)

  Ren : Semantics d LVar (Tm d ∞)
  Ren .th^𝓥 = th^LVar
  Ren .var = `var
  Ren {d} .alg = `con ∘
    map-s id-SkewLeftSemimoduleRel d
          (λ where refl → reify {𝓒 = Tm d ∞} (mk (extend′ ⊴*-refl))) refl

  th^Tm : Thinnable (Tm d ∞ A)
  th^Tm t th = semantics Ren th t

  vl^Tm : VarLike (Tm d ∞)
  vl^Tm .get .M = [ 0ᴹ │ 1ᴹ ]
  vl^Tm .get {RΘ = ctx R Θ} .sums =
    unrowL₂ (*ᴹ-0ᴹ (row R)) ++₂ unrowL₂ (*ᴹ-1ᴹ _)
  vl^Tm .get .lookup (ivar i q) = `var (lvar (↘ i) q (⊴*-refl ++₂ ⊴*-refl))

  Sub : Semantics d (Tm d ∞) (Tm d ∞)
  Sub .th^𝓥 = th^Tm
  Sub .var = id
  Sub {d} .alg = `con ∘
    map-s id-SkewLeftSemimoduleRel d
          (λ where refl → reify {𝓒 = Tm d ∞} vl^Tm) refl
