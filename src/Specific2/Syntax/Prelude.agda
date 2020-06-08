{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ)

module Specific2.Syntax.Prelude (algebra : SkewSemiring 0ℓ 0ℓ) where

  open SkewSemiring algebra public
    renaming (Carrier to Ann; _≤_ to _⊴_; refl to ⊴-refl; trans to ⊴-trans)
  open import Algebra.Skew.Definitions _⊴_

  open import Specific2.Syntax Ann _⊴_ 0# _+_ 1# _*_
  open import Generic.Linear.Syntax Ty Ann

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Vector.Properties
  open import Data.LTree.Matrix
  open import Data.LTree.Matrix.Properties
  open import Data.Product
  open import Relation.Binary.Definitions using (Reflexive; Transitive)
  open import Relation.Binary.PropositionalEquality

  +-interchange : Interchangable _+_ _+_
  +-interchange w x y z =
    ⊴-trans
      (+.assoc-→ w x (y + z))
      (⊴-trans
        (+.mono ⊴-refl
                (⊴-trans
                  (+.assoc-← x y z)
                  (⊴-trans
                    (+.mono (+.comm x y) ⊴-refl)
                    (+.assoc-→ y x z))))
        (+.assoc-← w y (x + z)))

  open Zero 0# public
  open Ident 0# 1# public
  open Mult 0# _+_ _*_ public
  open Mult-cong 0# _+_ _*_ _⊴_ _⊴_ _⊴_ ⊴-refl +.mono *.mono public
    renaming (*ᴹ-cong to *ᴹ-mono)
  open Plus-cong _+_ _⊴_ _⊴_ _⊴_ +.mono public renaming (+ᴹ-cong to +ᴹ-mono)
  open IdentMult 0# 1# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
    +.mono (proj₁ +.identity-→ , proj₂ +.identity-←)
    (proj₁ *.identity) (proj₁ annihil) public
  open MultIdent 0# 1# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
    +.mono (proj₁ +.identity-← , proj₂ +.identity-→)
    (proj₂ *.identity) (proj₂ annihil) public
  open PlusMult _+_ _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
    +.mono (+.identity-← .proj₁ 0#) +-interchange (proj₁ distrib) public
  open ZeroMult 0# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
    +.mono (+.identity-→ .proj₁ 0#) (proj₁ annihil) public
  open MultZero 0# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
    +.mono (+.identity-← .proj₁ 0#) (proj₂ annihil) public
  open LeftScaleMult _⊴_ 0# _+_ 0# _+_ _*_ _*_ _*_ _*_ ⊴-refl ⊴-trans
    +.mono (proj₂ annihil) (proj₂ distrib) *.assoc public
  open Cong2 _⊴_ +.mono public renaming (cong₂ to +*-mono)

  ⊴*-refl : ∀ {s} → Reflexive (_⊴*_ {s = s})
  ⊴*-refl .get i = ⊴-refl
  ⊴*-trans : ∀ {s} → Transitive (_⊴*_ {s = s})
  ⊴*-trans PQ QR .get i = ⊴-trans (PQ .get i) (QR .get i)

  ⊴ᴹ-refl : ∀ {s t} → Reflexive (_⊴ᴹ_ {s = s} {t})
  ⊴ᴹ-refl .get i j = ⊴-refl
  ⊴ᴹ-trans : ∀ {s t} → Transitive (_⊴ᴹ_ {s = s} {t})
  ⊴ᴹ-trans MN NO .get i j = ⊴-trans (MN .get i j) (NO .get i j)
