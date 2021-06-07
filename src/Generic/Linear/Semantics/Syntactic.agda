{-# OPTIONS --safe --sized-types --without-K --postfix-projections #-}

open import Algebra.Po
open import Level

module Generic.Linear.Semantics.Syntactic
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring
    renaming (Carrier to Ann
             ; _≤_ to _⊴_
             ; refl to ⊴-refl; trans to ⊴-trans
             )

  open import Algebra.Po.Relation
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.Product
  open import Function.Base using (id; _∘_)
  open import Size
  open import Relation.Unary
  open import Relation.Unary.Bunched
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring
  open import Generic.Linear.Syntax.Interpretation.Map Ty poSemiring
  open import Generic.Linear.Syntax.Term Ty rawPoSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Environment Ty poSemiring
  open import Generic.Linear.Thinning Ty poSemiring
  open import Generic.Linear.Extend Ty poSemiring
  open import Generic.Linear.Thinning.Properties Ty poSemiring
  open import Generic.Linear.Environment.Properties Ty poSemiring
  open import Generic.Linear.Semantics Ty poSemiring

  private
    variable
      fl : PremisesFlags
      d : System fl
      A : Ty
      v c : Level
      𝓥 : Scoped v
      𝓒 : Scoped c
      RΘ : Ctx

  record Kit (d : System fl) (𝓥 : Scoped v) : Set (suc 0ℓ ⊔ v) where
    field
      th^𝓥 : ∀ {A} → Thinnable (𝓥 A)
      var : ∀ {A} → ∀[ LVar A ⇒ 𝓥 A ]
      trm : ∀ {A} → ∀[ 𝓥 A ⇒ Tm d ∞ A ]

    psh^𝓥 : IsPresheaf 𝓥
    psh^𝓥 QP v = th^𝓥 v (subuse-th QP)

    instance
      flv : FromLVar 𝓥
      flv .fromLVar = var

  open Semantics

  reify : {{FromLVar 𝓥}} → ∀[ Kripke 𝓥 𝓒 RΘ A ⇒ Scope 𝓒 RΘ A ]
  reify b = b extendʳ .app✴ (+*-identity↘ _ ++₂ +*-identity↙ _) extendˡ

  module _ where
    open Kit

    kit→sem : Kit d 𝓥 → Semantics d 𝓥 (Tm d ∞)
    kit→sem K .th^𝓥 = K .th^𝓥
    kit→sem K .var = K .trm
    kit→sem {d = d} K .alg = `con ∘ map-s′ d (reify {𝓒 = Tm d ∞} {{flv K}})

  Ren : Semantics d LVar (Tm d ∞)
  Ren = kit→sem record { th^𝓥 = th^LVar ; var = id ; trm = `var }

  th^Tm : Thinnable (Tm d ∞ A)
  th^Tm t th = semantics Ren th t

  instance
    flv^Tm : FromLVar (Tm d ∞)
    flv^Tm .fromLVar = `var

  Sub : Semantics d (Tm d ∞) (Tm d ∞)
  Sub = kit→sem record { th^𝓥 = th^Tm ; var = `var ; trm = id }
