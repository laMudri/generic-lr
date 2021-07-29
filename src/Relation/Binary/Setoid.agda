{-# OPTIONS --safe --without-K --postfix-projections #-}

module Relation.Binary.Setoid where

  open import Level
  open import Relation.Binary

  record REL= {c0 c1 ℓ0 ℓ1} (X : Setoid c0 ℓ0) (Y : Setoid c1 ℓ1) r
         : Set (suc r ⊔ c0 ⊔ c1 ⊔ ℓ0 ⊔ ℓ1) where
    open Setoid
    field
      rel : REL (X .Carrier) (Y .Carrier) r
      resp-≈ : ∀ {x x′ y y′} → X ._≈_ x x′ → Y ._≈_ y y′ → rel x y → rel x′ y′
  open REL= public

  Rel= : ∀ {c ℓ} → Setoid c ℓ → ∀ r → Set (suc r ⊔ c ⊔ ℓ)
  Rel= X r = REL= X X r

  ≈-Rel= : ∀ {c ℓ} (X : Setoid c ℓ) → Rel= X ℓ
  ≈-Rel= X = record
    { rel = _≈_
    ; resp-≈ = λ xx yy xy → trans (sym xx) (trans xy yy)
    } where open Setoid X
