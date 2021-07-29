{-# OPTIONS --safe --without-K --postfix-projections --prop #-}

open import Algebra.Po
open import Level

module Generic.Linear.Variable.Equality
  (Ty : Set) (rawPoSemiring : RawPoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open RawPoSemiring rawPoSemiring renaming (Carrier to Ann)

  open import Generic.Linear.Variable Ty rawPoSemiring

  open import Data.Wrap
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

  infix 4 _≈ᵛ_

  _≈ᵛ_ : ∀ {Γ A} → Rel (Γ ∋ A) 0ℓ
  _≈ᵛ_ = Wrap λ i j → i .idx ≡ j .idx

  ≈ᵛ-refl : ∀ {Γ A} → Reflexive (_≈ᵛ_ {Γ} {A})
  ≈ᵛ-refl = [ ≡.refl ]
