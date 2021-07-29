------------------------------------------------------------------------
-- The Agda standard library
--
-- Like Data.Wrap, but based on Product⊤ rather than Product.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Wrap.Top where

open import Data.Product.Nary.NonDependent
open import Function.Nary.NonDependent
open import Level using (Level)
open import Relation.Nary

private
  variable
    ℓ : Level

record Wrap′ {n} {ls} {A : Sets n ls} (F : A ⇉ Set ℓ) (xs : Product⊤ n A)
                  : Set ℓ where
  constructor [_]
  field
    get : uncurry⊤ₙ n F xs

open Wrap′ public

Wrap : ∀ {n ls} {A : Sets n ls} → A ⇉ Set ℓ → A ⇉ Set ℓ
Wrap {n = n} F = curry⊤ₙ n (Wrap′ F)
