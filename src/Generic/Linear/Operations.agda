{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Po
open import Relation.Binary using (Rel; REL)
open import Level using (0ℓ; suc)

module Generic.Linear.Operations (rawPoSemiring : RawPoSemiring 0ℓ 0ℓ 0ℓ) where

  open RawPoSemiring rawPoSemiring renaming (Carrier to Ann)

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.Nat.Base using (ℕ; zero; suc)
  open import Data.Product
  open import Data.Product.Nary.NonDependent
  open import Function.Base
  open import Function.Nary.NonDependent
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_)
  open import Relation.Nary

  -- _≤0 _≤[_+_] _≤[_*_]
  infix 4 _≈*_ _≤*_ _≤0* _≤[_+*_] _≤[_*ₗ_]
  infixr 6 _+*_
  infixr 8 _*ₗ_

  -- _≤0 : Ann → Set
  -- _≤0 = _≤ 0#
  -- _≤[_+_] _≤[_*_] : (x y z : Ann) → Set
  -- x ≤[ y + z ] = x ≤ y + z
  -- x ≤[ y * z ] = x ≤ y * z

  _≈*_ = Liftₙ _≈_
  _≤*_ = Liftₙ _≤_
  0* = lift₀ 0#
  _+*_ = lift₂ _+_

  _*ₗ_ : Ann → ∀ {s} → Vector Ann s → Vector Ann s
  ρ *ₗ R = lift₁ (ρ *_) R

  ⟨_∣ : ∀ {s} → Ptr s → Vector Ann s
  ⟨_∣ = 1ᴹ  where open Ident 0# 1#

  _≤0* : ∀ {s} → Vector Ann s → Set
  _≤0* = Liftₙ (_≤ 0#)
  _≤[_+*_] : ∀ {s} → (R P Q : Vector Ann s) → Set
  _≤[_+*_] = Liftₙ λ z x y → z ≤ x + y
  _≤[_*ₗ_] : ∀ {s} → Vector Ann s → Ann → Vector Ann s → Set
  R ≤[ r *ₗ P ] = (Liftₙ λ z x → z ≤ r * x) R P

  -- Conversion between n-ary relations and _≤*_

  0*→≤* : ∀ {s} {R : Vector _ s} → R ≤0* → R ≤* 0*
  0*→≤* sp0 .get i = sp0 .get i
  +*→≤* : ∀ {s} {P Q R : Vector _ s} → R ≤[ P +* Q ] → R ≤* P +* Q
  +*→≤* sp+ .get i = sp+ .get i
  *ₗ→≤* : ∀ {s r} {P R : Vector _ s} → R ≤[ r *ₗ P ] → R ≤* r *ₗ P
  *ₗ→≤* sp* .get i = sp* .get i

  ≤*→0* : ∀ {s} {R : Vector _ s} → R ≤* 0* → R ≤0*
  ≤*→0* sp0 .get i = sp0 .get i
  ≤*→+* : ∀ {s} {P Q R : Vector _ s} → R ≤* P +* Q → R ≤[ P +* Q ]
  ≤*→+* sp+ .get i = sp+ .get i
  ≤*→*ₗ : ∀ {s r} {P R : Vector _ s} → R ≤* r *ₗ P → R ≤[ r *ₗ P ]
  ≤*→*ₗ sp* .get i = sp* .get i
