{-# OPTIONS --safe --without-K #-}

module Function.Extra where

  open import Function.Base

  -- Tight-binding infix version of a function
  infix 20 _⟨_⟩⊢_
  _⟨_⟩⊢_ = _⟨_⟩_
