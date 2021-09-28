{-# OPTIONS --safe --without-K #-}

module Data.Bool.Extra where

  open import Data.Bool.Base
  open import Data.Unit.Polymorphic using (⊤; tt)
  open import Data.Wrap
  open import Level

  private
    variable
      ℓ x y z : Level
      X : Set x
      Y : Set y
      Z : Set z

  If : Bool → Set ℓ → Set ℓ
  If = Wrap λ where
    false X → ⊤
    true X → X

  map-If : (X → Y) → ∀ {b} → If b X → If b Y
  map-If f {false} _ = _
  map-If f {true} [ x ] = [ f x ]

  for-If : ∀ {b} → If b X → (X → Y) → If b Y
  for-If x f = map-If f x

  pure-If : X → ∀ {b} → If b X
  pure-If x {false} = _
  pure-If x {true} = [ x ]

  zip-If : (X → Y → Z) → ∀ {b} → If b X → If b Y → If b Z
  zip-If f {false} x y = _
  zip-If f {true} [ x ] [ y ] = [ f x y ]
