{-# OPTIONS --without-K #-}

module Algebra.Po.Construct.Nat where

  open import Algebra.Po
  open import Data.Nat
  open import Data.Nat.Properties
  open import Level
  open import Relation.Binary.PropositionalEquality

  ℕ-poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ
  ℕ-poSemiring = record
    { Carrier = ℕ
    ; _≈_ = _≡_
    ; _≤_ = _≤_
    ; 0# = 0
    ; _+_ = _+_
    ; 1# = 1
    ; _*_ = _*_
    ; isPoSemiring = record
      { isPartialOrder = ≤-isPartialOrder
      ; isSemiring = +-*-isSemiring
      ; +-mono = +-mono-≤
      ; *-mono = *-mono-≤
      }
    }
