{-# OPTIONS --safe --without-K #-}

open import Level

module Relation.Unary.Checked {ℓ : Level} where

  open import Relation.Unary as Syn public using (Pred)

  open import Data.Unit.Polymorphic
  open import Data.Product

  private
    variable
      a b : Level
      A : Set a
      B : Set b

  infixr 8 _⇒_
  infixr 7 _∩_
  infix 4 _⊆_

  U : Pred A ℓ
  U _ = ⊤

  _∩_ : (P Q : Pred A ℓ) → Pred A ℓ
  _∩_ = Syn._∩_

  _⇒_ : (P Q : Pred A ℓ) → Pred A ℓ
  _⇒_ = Syn._⇒_

  _⊆_ : (P Q : Pred A ℓ) → Set _
  _⊆_ = Syn._⊆_
