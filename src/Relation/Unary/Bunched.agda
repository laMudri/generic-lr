{-# OPTIONS --safe --without-K #-}

module Relation.Unary.Bunched {a} {A : Set a} where

  open import Level
  open import Relation.Unary

  module BunchedUnit {ℓ} (_∼0 : A → Set ℓ) where

    record ✴1 (x : A) : Set ℓ where
      constructor ✴1⟨_⟩
      field
        split : x ∼0

  open BunchedUnit public using (✴1⟨_⟩)

  module BunchedConjunction {ℓ} (_∼_+_ : A → A → A → Set ℓ) where

    infixr 8 _─✴_
    infixr 9 _✴_

    record _✴_ {t u} (T : A → Set t) (U : A → Set u) (x : A)
               : Set (a ⊔ ℓ ⊔ t ⊔ u) where
      constructor _✴⟨_⟩_
      field
        {y z} : A
        T-prf : T y
        split : x ∼ y + z
        U-prf : U z

    record _─✴_ {t u} (T : A → Set t) (U : A → Set u) (x : A)
                : Set (a ⊔ ℓ ⊔ t ⊔ u) where
      constructor lam✴
      field
        app✴ : ∀ {y z} (split : z ∼ x + y) (T-prf : T y) → U z
    open _─✴_ public

  open BunchedConjunction public using (_✴⟨_⟩_; lam✴; app✴)

  module BunchedScaling {r ℓ} {R : Set r} (_∼_*ₗ_ : A → R → A → Set ℓ) where

    infixr 10 _·_

    record _·_ {t} (r : R) (T : A → Set t) (x : A) : Set (a ⊔ ℓ ⊔ t) where
      constructor ⟨_⟩·_
      field
        {z} : A
        split : x ∼ r *ₗ z
        T-prf : T z

  open BunchedScaling public using (⟨_⟩·_)
