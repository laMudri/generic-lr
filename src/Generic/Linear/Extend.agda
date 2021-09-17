{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Po
open import Level

module Generic.Linear.Extend
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring renaming (Carrier to Ann)

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.Product
  open import Relation.Unary

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Environment Ty poSemiring

  record FromLVar {ℓ} (_𝓥_ : OpenFam ℓ) : Set (suc 0ℓ ⊔ ℓ) where
    field fromLVar : ∀ {A} → ∀[ _∋ A ⇒ _𝓥 A ]

    extendˡ : ∀ {RΘ s Γ} → [ _𝓥_ ] ctx {s} 0* Γ ++ᶜ RΘ ⇒ᵉ RΘ
    extendˡ .Ψ = [ 0ᴹ │ 1ᴹ ]
    extendˡ .asLinRel = [ 0AsLinRel │ idAsLinRel ]AsLinRel
    extendˡ .sums = 0*-triv , ≤*-refl
    extendˡ .lookup (sp0 , le) (lvar i q b) =
      fromLVar (lvar (↘ i) q (0*→≤* sp0 ++ₙ ≤*-trans le b))

    extendʳ : ∀ {RΘ s Γ} → [ _𝓥_ ] RΘ ++ᶜ ctx {s} 0* Γ ⇒ᵉ RΘ
    extendʳ .Ψ = [ 1ᴹ │ 0ᴹ ]
    extendʳ .asLinRel = [ idAsLinRel │ 0AsLinRel ]AsLinRel
    extendʳ .sums = ≤*-refl , 0*-triv
    extendʳ .lookup (le , sp0) (lvar i q b) =
      fromLVar (lvar (↙ i) q (≤*-trans le b ++ₙ 0*→≤* sp0))

  open FromLVar {{...}} public

  instance
    flv^LVar : FromLVar _∋_
    flv^LVar .fromLVar v = v
