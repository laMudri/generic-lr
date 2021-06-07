{-# OPTIONS --safe --without-K #-}

open import Algebra.Po
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel)

module Generic.Linear.Variable
  (Ty : Set) (rawPoSemiring : RawPoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open RawPoSemiring rawPoSemiring renaming (Carrier to Ann; _≤_ to _⊴_)

  open import Relation.Binary.PropositionalEquality

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Syntax Ty Ann

  record LVar (A : Ty) (PΓ : Ctx) : Set where
    constructor lvar

    open Ctx PΓ renaming (s to s; Γ to Γ; R to P)

    field
      idx : Ptr s
      tyq : Γ idx ≡ A
      basis : P ⊴* 1ᴹ idx
  open LVar public