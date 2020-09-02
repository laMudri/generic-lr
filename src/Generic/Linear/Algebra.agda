{-# OPTIONS --safe --without-K #-}

open import Algebra.Skew
open import Level using (0ℓ)

module Generic.Linear.Algebra (skewSemiring : SkewSemiring 0ℓ 0ℓ) where

  open SkewSemiring skewSemiring
    renaming (Carrier to Ann
             ; _≤_ to _⊴_
             ; refl to ⊴-refl; trans to ⊴-trans
             )

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Vector.Properties
  open import Data.LTree.Matrix
  open import Data.LTree.Matrix.Properties
  open import Data.Product

  open import Generic.Linear.Operations rawSkewSemiring

  private
    variable
      s : LTree
      P Q R : Vector Ann s

  ⊴*-refl : P ⊴* P
  ⊴*-refl .get i = ⊴-refl

  ⊴*-trans : P ⊴* Q → Q ⊴* R → P ⊴* R
  ⊴*-trans PQ QR .get i = ⊴-trans (PQ .get i) (QR .get i)

  open Reflᴹ _⊴_ ⊴-refl public renaming (reflᴹ to ⊴ᴹ-refl)
  open Transᴹ _⊴_ ⊴-trans public renaming (transᴹ to ⊴ᴹ-trans)
  open Cong2 _⊴_ +-mono public renaming (cong₂ to +*-mono) public
  open Mult-cong 0# _+_ _*_ _⊴_ _⊴_ _⊴_ ⊴-refl +-mono *-mono public
    renaming (*ᴹ-cong to *ᴹ-mono)
  open IdentMult 0# 1# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans +-mono
                 (+.identity-→ .proj₁ , +.identity-← .proj₂)
                 (*.identity .proj₁) (annihil .proj₁) public
  open MultIdent 0# 1# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
                 +-mono (+.identity-← .proj₁ , +.identity-→ .proj₂)
                 (*.identity .proj₂) (annihil .proj₂) public
  open ZeroMult 0# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans +-mono
                (+.identity-→ .proj₁ 0#) (annihil .proj₁) public
  open MultZero 0# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
                +-mono (+.identity-← .proj₁ 0#) (annihil .proj₂) public
  open PlusMult _+_ _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans +-mono
                (+.identity-← .proj₁ 0#) +.inter (distrib .proj₁) public
  open LeftScaleMult _⊴_ 0# _+_ 0# _+_ _*_ _*_ _*_ _*_ ⊴-refl ⊴-trans +-mono
                     (annihil .proj₂) (distrib .proj₂) *.assoc public
  open MultMult _⊴_ 0# _+_ 0# _+_ 0# _+_ _*_ _*_ _*_ _*_ ⊴-refl ⊴-trans
                +-mono (+.identity-→ .proj₁ 0#) (+.identity-← .proj₁ 0#)
                +.inter *.assoc
                (annihil .proj₁) (λ a b c → distrib .proj₁ b c a)
                (annihil .proj₂) (distrib .proj₂) public
