{-# OPTIONS --safe --without-K #-}

module Relation.Unary.Bunched.Synth {a} {A : Set a} where

  import Relation.Unary.Bunched as B
  open B public using
    ( module BunchedConjunction; module BunchedScaling
    ; module BunchedDuplicable; module BunchedOrder
    ; ◇⟨_⟩_; ℑ⟨_⟩; _✴⟨_⟩_; lam✴; app✴; ⟨_⟩·_; □⟨_,_,_⟩_
    )

  open import Data.Product
  open import Level
  open import Relation.Unary

  module BunchedUnit {ℓ} (_∼0 : A → Set ℓ) where

    private
      module Chk = B.BunchedUnit _∼0
    open Chk public using (ℑ⟨_⟩)

    ℑ : A → Set ℓ
    ℑ = Chk.ℑ {v = 0ℓ}
