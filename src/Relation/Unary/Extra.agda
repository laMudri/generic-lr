{-# OPTIONS --safe --without-K #-}

module Relation.Unary.Extra where

  open import Relation.Unary

  -- TODO: move somewhere else (Relation.Unary.Extras?)

  I⋂ : ∀ {a i ℓ} {A : Set a} (I : Set i) → (I → Pred A ℓ) → Pred A _
  I⋂ I P = λ x → {i : I} → P i x
