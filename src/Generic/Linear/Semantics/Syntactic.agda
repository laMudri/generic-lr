{-# OPTIONS --safe --sized-types --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (Level; 0ℓ)

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
  open import Relation.Unary.Bunched
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
  open import Generic.Linear.Extend Ty skewSemiring
  open import Generic.Linear.Thinning.Properties Ty skewSemiring
  open import Generic.Linear.Environment.Properties Ty skewSemiring
  open import Generic.Linear.Semantics Ty skewSemiring

  private
    variable
      d : System
      A : Ty
      v c : Level
      𝓥 : Scoped v
      𝓒 : Scoped c
      RΘ : Ctx

  open Semantics

  reify : {{LeftExtend 𝓥}} → ∀[ Kripke 𝓥 𝓒 RΘ A ⇒ Scope 𝓒 RΘ A ]
  reify b = b extendʳ .app✴ (+*-identity↘ _ ++₂ +*-identity↙ _) extendˡ

  Ren : Semantics d LVar (Tm d ∞)
  Ren .th^𝓥 = th^LVar
  Ren .var = `var
  Ren {d} .alg = `con ∘ map-s′ d (reify {𝓒 = Tm d ∞})

  th^Tm : Thinnable (Tm d ∞ A)
  th^Tm t th = semantics Ren th t

  instance
    re^Tm : RightExtend (Tm d ∞)
    re^Tm .embedVarʳ v = `var (embedVarʳ v)

    le^Tm : LeftExtend (Tm d ∞)
    le^Tm .embedVarˡ v = `var (embedVarˡ v)

  Sub : Semantics d (Tm d ∞) (Tm d ∞)
  Sub .th^𝓥 = th^Tm
  Sub .var = id
  Sub {d} .alg = `con ∘ map-s′ d (reify {𝓒 = Tm d ∞})
