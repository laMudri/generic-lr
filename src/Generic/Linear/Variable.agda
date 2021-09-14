{-# OPTIONS --safe --without-K #-}

open import Algebra.Po
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel)

module Generic.Linear.Variable
  (Ty : Set) (rawPoSemiring : RawPoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open RawPoSemiring rawPoSemiring renaming (Carrier to Ann)

  open import Relation.Binary.PropositionalEquality

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Syntax Ty Ann

  infix 20 _∋_

  record _∋_ (Γ : Ctx) (A : Ty) : Set where
    constructor lvar

    open Ctx Γ renaming (shape to s; ty-ctx to γ; use-ctx to P)

    field
      idx : Ptr s
      tyq : γ idx ≡ A
      basis : P ≤* ⟨ idx ∣
  open _∋_ public
