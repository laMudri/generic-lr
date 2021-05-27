{-# OPTIONS --safe --without-K --prop #-}

module Proposition where

  infixr 3 _∨ᴾ_

  data ⊥ᴾ : Prop where
  record ⊤ᴾ : Prop where
    instance constructor tt

  data _∨ᴾ_ (P Q : Prop) : Prop where
    instance
      inl : {{P}} → P ∨ᴾ Q
      inr : {{Q}} → P ∨ᴾ Q
