{-# OPTIONS --safe --sized-types --without-K #-}

open import Algebra.Skew
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel)

module Generic.Linear.Syntax.Term
  (Ty : Set) (rawSkewSemiring : RawSkewSemiring 0ℓ 0ℓ)
  where

  open RawSkewSemiring rawSkewSemiring renaming (Carrier to Ann; _≤_ to _⊴_)

  open import Size
  open import Relation.Unary

  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawSkewSemiring
  open import Generic.Linear.Thinning Ty rawSkewSemiring

  private
    variable
     A : Ty
     sz : Size
     fl : PremisesFlags

  data Tm (d : System fl) : Size → Scoped 0ℓ where
    `var : ∀[ LVar                     A ⇒ Tm d (↑ sz) A ]
    `con : ∀[ ⟦ d ⟧s (Scope (Tm d sz)) A ⇒ Tm d (↑ sz) A ]
