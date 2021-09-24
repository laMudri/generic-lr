{-# OPTIONS --sized-types --without-K --prop #-}

open import Algebra.Po
open import Level

module Generic.Linear.Syntax.Term
  (Ty : Set) (rawPoSemiring : RawPoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open RawPoSemiring rawPoSemiring renaming (Carrier to Ann)

  open import Function.Extra
  open import Size
  open import Relation.Nary

  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring

  private
    variable
     sz : Size
     fl : PremisesFlags

  infix 20 [_,_]_⊢_

  data [_,_]_⊢_ (d : System fl) : Size → OpenFam 0ℓ where
    `var : ∀[                          _∋_ ⇒ [ d , ↑ sz ]_⊢_ ]
    `con : ∀[ ⟦ d ⟧s (Scope [ d , sz ]_⊢_) ⇒ [ d , ↑ sz ]_⊢_ ]
