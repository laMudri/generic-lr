{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra using (Op₂)
import Algebra.Definitions as Defs
open import Function.Base
open import Level using (0ℓ)
open import Relation.Binary using (Rel; Reflexive; Transitive)

module Specific.Syntax.Prelude
  (Ann : Set) (_⊴_ : Rel Ann 0ℓ)
  (0# : Ann) (_+_ : Op₂ Ann) (1# : Ann) (_*_ : Op₂ Ann)
  (⊴-refl : Reflexive _⊴_) (⊴-trans : Transitive _⊴_)
  (open Defs _⊴_) (let module ⊵ = Defs (flip _⊴_))
  (+-mono : Congruent₂ _+_) (*-mono : Congruent₂ _*_)
  (+-identity-⊴ : Identity 0# _+_) (+-identity-⊵ : ⊵.Identity 0# _+_)
  (+-interchange : Interchangable _+_ _+_)
  (1-* : ∀ x → (1# * x) ⊴ x) (*-1 : ∀ x → x ⊴ (x * 1#)) (*-* : Associative _*_)
  (0-* : ∀ x → (0# * x) ⊴ 0#) (*-0 : ∀ x → 0# ⊴ (x * 0#))
  (+-* : ∀ x y z → ((x + y) * z) ⊴ ((x * z) + (y * z)))
  (*-+ : ∀ x y z → ((x * y) + (x * z)) ⊴ (x * (y + z)))
  where

  open import Specific.Syntax Ann _⊴_ 0# _+_ 1# _*_
  open import Generic.Linear.Syntax Ty Ann

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Vector.Properties
  open import Data.LTree.Matrix
  open import Data.LTree.Matrix.Properties
  open import Data.Product
  open import Relation.Binary.PropositionalEquality

  open Ident 0# 1# public
  open Mult 0# _+_ _*_ public
  open Mult-cong 0# _+_ _*_ _⊴_ _⊴_ _⊴_ ⊴-refl +-mono *-mono public
    renaming (*ᴹ-cong to *ᴹ-mono)
  open Plus-cong _+_ _⊴_ _⊴_ _⊴_ +-mono public renaming (+ᴹ-cong to +ᴹ-mono)
  open IdentMult 0# 1# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
    +-mono +-identity-⊴ 1-* 0-* public
  open MultIdent 0# 1# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
    +-mono +-identity-⊵ *-1 *-0 public
  open PlusMult _+_ _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
    +-mono (+-identity-⊵ .proj₂ 0#) +-interchange +-* public
  open ZeroMult 0# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
    +-mono (+-identity-⊴ .proj₁ 0#) 0-* public
  open MultZero 0# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
    +-mono (+-identity-⊵ .proj₂ 0#) *-0 public
  open LeftScaleMult _⊴_ 0# _+_ 0# _+_ _*_ _*_ _*_ _*_ ⊴-refl ⊴-trans
    +-mono *-0 *-+ *-* public
  open Cong2 _⊴_ +-mono public renaming (cong₂ to +*-mono)

  ⊴*-refl : ∀ {s} → Reflexive (_⊴*_ {s = s})
  ⊴*-refl .get i = ⊴-refl
  ⊴*-trans : ∀ {s} → Transitive (_⊴*_ {s = s})
  ⊴*-trans PQ QR .get i = ⊴-trans (PQ .get i) (QR .get i)

  ⊴ᴹ-refl : ∀ {s t} → Reflexive (_⊴ᴹ_ {s = s} {t})
  ⊴ᴹ-refl .get i j = ⊴-refl
  ⊴ᴹ-trans : ∀ {s t} → Transitive (_⊴ᴹ_ {s = s} {t})
  ⊴ᴹ-trans MN NO .get i j = ⊴-trans (MN .get i j) (NO .get i j)
