{-# OPTIONS --safe --without-K #-}

module Relation.Unary.Extra where

  open import Level using (Level; _⊔_)
  open import Relation.Unary

  I⋂ : ∀ {a i ℓ} {A : Set a} (I : Set i) → (I → Pred A ℓ) → Pred A _
  I⋂ I P = λ x → {i : I} → P i x
