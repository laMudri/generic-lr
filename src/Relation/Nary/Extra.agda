{-# OPTIONS --safe --without-K #-}

module Relation.Nary.Extra where

  open import Level
  open import Function.Nary.NonDependent
  open import Relation.Nary

  infix 4 _⊆_

  _⊆_ : ∀ {n} {as r s} {As : Sets n as} →
    As ⇉ Set r → As ⇉ Set s → Set (r ⊔ s ⊔ ⨆ n as)
  R ⊆ S = ∀[ R ⇒ S ]
