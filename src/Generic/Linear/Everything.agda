{-# OPTIONS --without-K --prop --sized-types #-}

open import Algebra.Po
open import Level using (Level; 0ℓ; _⊔_)
open import Relation.Binary using (Rel)

module Generic.Linear.Everything
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring public renaming (Carrier to Ann)

  open import Generic.Linear.Operations rawPoSemiring public
  open import Generic.Linear.Algebra poSemiring public
  open import Generic.Linear.Syntax Ty Ann public
  open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring public
  open import Generic.Linear.Syntax.Interpretation.Map Ty poSemiring public
  open import Generic.Linear.Syntax.Term Ty rawPoSemiring public
  open import Generic.Linear.Variable Ty rawPoSemiring public
  open import Generic.Linear.Environment Ty poSemiring public
  open import Generic.Linear.Environment.Categorical Ty poSemiring public
  open import Generic.Linear.Environment.Properties Ty poSemiring public
  open import Generic.Linear.Renaming Ty poSemiring public
  open import Generic.Linear.Renaming.Properties Ty poSemiring public
  open import Generic.Linear.Renaming.Monoidal Ty poSemiring public
  open import Generic.Linear.Semantics Ty poSemiring public
  open import Generic.Linear.Semantics.Syntactic Ty poSemiring public
