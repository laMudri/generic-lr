{-# OPTIONS --safe --sized-types --without-K #-}

open import Algebra.Po
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel)

module Generic.Linear.Syntax.Term
  (Ty : Set) (rawPoSemiring : RawPoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open RawPoSemiring rawPoSemiring renaming (Carrier to Ann; _≤_ to _⊴_)

  open import Size
  open import Relation.Unary

  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring

  private
    variable
     A : Ty
     sz : Size
     fl : PremisesFlags

  data Tm (d : System fl) : Size → Scoped 0ℓ where
    `var : ∀[ LVar                     A ⇒ Tm d (↑ sz) A ]
    `con : ∀[ ⟦ d ⟧s (Scope (Tm d sz)) A ⇒ Tm d (↑ sz) A ]
