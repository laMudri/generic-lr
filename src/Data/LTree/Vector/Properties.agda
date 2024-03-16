{-# OPTIONS --safe --without-K #-}

module Data.LTree.Vector.Properties where

  open import Algebra.Core using (Op₂)
  import Algebra.Definitions as Defs
  open import Data.Bool
  open import Data.Product
  open import Function.Base using (_∘_)
  open import Level using (Level)
  open import Relation.Binary using (Rel)
  open import Relation.Binary.Definitions
  import Relation.Binary.Reasoning.Base.Single as Rea

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix using (Matrix; leftᴹ; rightᴹ)

  private
    variable
      a b r : Level
      A : Set a
      B : Set b
      s t : LTree

  module Cong2
    (_≈_ : Rel A r) {_+_ : Op₂ A} (+-cong : Defs.Congruent₂ _≈_ _+_)
    where

    cong₂ : Defs.Congruent₂ (Liftₙ _≈_ {s}) (lift₂ _+_)
    cong₂ uu vv .get i = +-cong (uu .get i) (vv .get i)

  module SumCong
    (_≈_ : Rel A r) (0# : A) (_+_ : Op₂ A) (open Defs _≈_)
    (0-cong : 0# ≈ 0#)
    (+-cong : Congruent₂ _+_)
    where

    open Sum 0# _+_

    ∑-cong : ∀ {s} {u v : Vector A s} → Liftₙ _≈_ u v → ∑ u ≈ ∑ v
    ∑-cong {[-]} (mk qs) = qs here
    ∑-cong {ε} (mk qs) = 0-cong
    ∑-cong {s <+> t} (mk qs) =
      +-cong (∑-cong (mk (qs ∘ ↙))) (∑-cong (mk (qs ∘ ↘)))

  module Sum0
    (_≈_ : Rel A r) (0# : A) (_+_ : Op₂ A)
    (open Defs _≈_)
    (trans : Transitive _≈_)
    (0-cong : 0# ≈ 0#)
    (+-cong : Congruent₂ _+_)
    (0+0 : (0# + 0#) ≈ 0#)
    where

    open Sum 0# _+_

    ∑-0 : ∀ s → ∑ {s} (λ _ → 0#) ≈ 0#
    ∑-0 [-] = 0-cong
    ∑-0 ε = 0-cong
    ∑-0 (s <+> t) = trans (+-cong (∑-0 s) (∑-0 t)) 0+0

  module Sum+
    (_≈_ : Rel A r) (0# : A) (_+_ : Op₂ A)
    (open Defs _≈_)
    (refl : Reflexive _≈_)
    (trans : Transitive _≈_)
    (+-cong : Congruent₂ _+_)
    (0+0 : 0# ≈ (0# + 0#))
    (exchange : Interchangable _+_ _+_)
    where

    open Sum 0# _+_

    ∑-+ : (u v : Vector A s) → ∑ (λ i → u i + v i) ≈ (∑ u + ∑ v)
    ∑-+ {[-]} u v = refl
    ∑-+ {ε} u v = 0+0
    ∑-+ {s <+> t} u v =
      trans (+-cong (∑-+ (u ∘ ↙) (v ∘ ↙))
                    (∑-+ (u ∘ ↘) (v ∘ ↘)))
            (exchange _ _ _ _)

  module SumLinear
    (0A : A) (_+A_ : Op₂ A)
    (_≈_ : Rel B r) (0B : B) (_+B_ : Op₂ B)
    (open Defs _≈_)
    (refl : Reflexive _≈_)
    (trans : Transitive _≈_)
    (+-cong : Congruent₂ _+B_)
    (f : A → B)
    (f-0 : f 0A ≈ 0B)
    (f-+ : ∀ x y → f (x +A y) ≈ (f x +B f y))
    where

    open Sum 0A _+A_ renaming (∑ to ∑A)
    open Sum 0B _+B_ renaming (∑ to ∑B)

    ∑-linear : ∀ {s} (u : Vector A s) → f (∑A u) ≈ ∑B (f ∘ u)
    ∑-linear {[-]} u = refl
    ∑-linear {ε} u = f-0
    ∑-linear {s <+> t} u =
      trans (f-+ (∑A (u ∘ ↙)) (∑A (u ∘ ↘)))
            (+-cong (∑-linear (u ∘ ↙)) (∑-linear (u ∘ ↘)))

  module SumComm
    (_≈_ : Rel A r) (0# : A) (_+_ : Op₂ A)
    (open Defs _≈_)
    (refl : Reflexive _≈_)
    (trans : Transitive _≈_)
    (+-cong : Congruent₂ _+_)
    (0+0-→ : (0# + 0#) ≈ 0#)
    (0+0-← : 0# ≈ (0# + 0#))
    (exchange : Interchangable _+_ _+_)
    where

    open Sum 0# _+_
    open Sum0 _≈_ 0# _+_ trans refl +-cong 0+0-→
    open Sum+ _≈_ 0# _+_ refl trans +-cong 0+0-← exchange

    ∑-comm : (M : Matrix A s t) →
             (∑ λ i → ∑ λ j → M i j) ≈ (∑ λ j → ∑ λ i → M i j)
    ∑-comm {s} {[-]} M = refl
    ∑-comm {s} {ε} M = ∑-0 s
    ∑-comm {s} {tl <+> tr} M =
      trans (∑-+ (λ i → ∑ (leftᴹ M i)) (λ i → ∑ (rightᴹ M i)))
            (+-cong (∑-comm (leftᴹ M)) (∑-comm (rightᴹ M)))
