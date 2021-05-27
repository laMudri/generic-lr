{-# OPTIONS --safe --without-K #-}

module Data.Hand where

  data Hand : Set where
    ll rr : Hand

  [_>_<_] : ∀ {ℓ} {X : Set ℓ} → X → Hand → X → X
  [ x > ll < y ] = x
  [ x > rr < y ] = y
