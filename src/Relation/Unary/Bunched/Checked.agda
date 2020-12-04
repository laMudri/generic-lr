{-# OPTIONS --safe --without-K #-}

module Relation.Unary.Bunched.Checked {a} {A : Set a} where

  import Relation.Unary.Bunched {a} {A} as B
  open B public using
    ( module BunchedUnit; module BunchedScaling
    ; ℑ⟨_⟩; _✴⟨_⟩_; lam✴; app✴; ⟨_⟩·_
    )

  open import Data.Product
  open import Level
  open import Relation.Unary

  module BunchedConjunction {ℓ} (_∼_+_ : A → A → A → Set ℓ) where

    private
      module Syn = B.BunchedConjunction _∼_+_

    infixr 8 _─✴_
    infixr 9 _✴_

    _✴_ _─✴_ : ∀ {v} (T : A → Set v) (U : A → Set v) → A → Set (a ⊔ ℓ ⊔ v)
    _✴_ = Syn._✴_
    _─✴_ = Syn._─✴_

    map-✴ : ∀ {v w} {T U : A → Set v} {T′ U′ : A → Set w} →
            ∀[ T ⇒ T′ ] × ∀[ U ⇒ U′ ] → ∀[ T ✴ U ⇒ T′ ✴ U′ ]
    map-✴ = Syn.map-✴
