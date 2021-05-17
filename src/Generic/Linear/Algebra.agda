{-# OPTIONS --safe --without-K #-}

open import Algebra.Po
open import Algebra.Skew
open import Level using (0ℓ)

module Generic.Linear.Algebra (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ) where

  open PoSemiring poSemiring
    renaming (Carrier to Ann
             ; _≤_ to _⊴_
             ; ≤-refl to ⊴-refl; ≤-trans to ⊴-trans; ≤-reflexive to ⊴-reflexive
             )

  open import Algebra.Definitions using (Interchangable)
  open import Data.LTree
  open import Data.LTree.Vector hiding (setoid)
  open import Data.LTree.Vector.Properties
  open import Data.LTree.Matrix
  open import Data.LTree.Matrix.Properties
  open import Data.Product

  open import Generic.Linear.Operations rawPoSemiring

  private
    variable
      s : LTree
      P Q R : Vector Ann s

      t : LTree
      M N O : Matrix Ann s t

  ⊴*-refl : P ⊴* P
  ⊴*-refl .get i = ⊴-refl

  ⊴*-trans : P ⊴* Q → Q ⊴* R → P ⊴* R
  ⊴*-trans PQ QR .get i = ⊴-trans (PQ .get i) (QR .get i)

  ≈*-sym : P ≈* Q → Q ≈* P
  ≈*-sym PQ .get i = sym (PQ .get i)

  ⊴*-reflexive : P ≈* Q → P ⊴* Q
  ⊴*-reflexive PQ .get i = ⊴-reflexive (PQ .get i)

  ≈ᴹ-refl : M ≈ᴹ M
  ≈ᴹ-refl .get i j = refl

  ≈ᴹ-trans : M ≈ᴹ N → N ≈ᴹ O → M ≈ᴹ O
  ≈ᴹ-trans MN NO .get i j = trans (MN .get i j) (NO .get i j)

  ≈ᴹ-sym : M ≈ᴹ N → N ≈ᴹ M
  ≈ᴹ-sym MN .get i j = sym (MN .get i j)

  ⊴ᴹ-reflexive : M ≈ᴹ N → M ⊴ᴹ N
  ⊴ᴹ-reflexive MN .get i j = ⊴-reflexive (MN .get i j)

  +*-identity↖ : (P : Vector Ann s) → 0* +* P ⊴* P
  +*-identity↖ P .get _ = +.identity-→ .proj₁ _
  +*-identity↗ : (P : Vector Ann s) → P +* 0* ⊴* P
  +*-identity↗ P .get _ = +.identity-← .proj₂ _
  +*-identity↙ : (P : Vector Ann s) → P ⊴* 0* +* P
  +*-identity↙ P .get _ = +.identity-← .proj₁ _
  +*-identity↘ : (P : Vector Ann s) → P ⊴* P +* 0*
  +*-identity↘ P .get _ = +.identity-→ .proj₂ _

  open Reflᴹ _⊴_ ⊴-refl public renaming (reflᴹ to ⊴ᴹ-refl)
  open Transᴹ _⊴_ ⊴-trans public renaming (transᴹ to ⊴ᴹ-trans)
  open Cong2 _⊴_ +-mono public renaming (cong₂ to +*-mono) public
  open Plus-cong _+_ _⊴_ _⊴_ _⊴_ +-mono public renaming (+ᴹ-cong to +ᴹ-mono)
  open Mult-cong 0# _+_ _*_ _⊴_ _⊴_ _⊴_ ⊴-refl +-mono *-mono public
    renaming (*ᴹ-cong to *ᴹ-mono)
  open IdentMult 0# 1# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans +-mono
                 (+.identity-→ .proj₁ , +.identity-← .proj₂)
                 (*.identity .proj₁) (≤-annihil .proj₁) public
  open MultIdent 0# 1# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
                 +-mono (+.identity-← .proj₁ , +.identity-→ .proj₂)
                 (*.identity .proj₂) (≤-annihil .proj₂) public
  open ZeroMult 0# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans +-mono
                (+.identity-→ .proj₁ 0#) (≤-annihil .proj₁) public
  open MultZero 0# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
                +-mono (+.identity-← .proj₁ 0#) (≤-annihil .proj₂) public
  open PlusMult _+_ _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans +-mono
                (+.identity-← .proj₁ 0#) +.inter (≤-distrib .proj₁) public
  open LeftScaleMult _⊴_ 0# _+_ 0# _+_ _*_ _*_ _*_ _*_ ⊴-refl ⊴-trans +-mono
                     (≤-annihil .proj₂) (≤-distrib .proj₂) *.assoc public
  open MultMult _⊴_ 0# _+_ 0# _+_ 0# _+_ _*_ _*_ _*_ _*_ ⊴-refl ⊴-trans
                +-mono (+.identity-→ .proj₁ 0#) (+.identity-← .proj₁ 0#)
                +.inter *.assoc
                (≤-annihil .proj₁) (λ a b c → ≤-distrib .proj₁ b c a)
                (≤-annihil .proj₂) (≤-distrib .proj₂) public

  open Mult-cong 0# _+_ _*_ _≈_ _≈_ _≈_ refl +-cong *-cong public
  open MultIdent
    0# 1# _≈_ 0# _+_ _*_ refl trans
    +-cong
    ((λ x → sym (+-identity .proj₁ x)) , (λ x → sym (+-identity .proj₂ x)))
    (λ x → sym (*-identity .proj₂ x)) (λ x → sym (zero .proj₂ x))
    renaming (*ᴹ-1ᴹ to *ᴹ-identityʳ˘)
  *ᴹ-identityʳ : ∀ {s t} (M : Matrix Ann s t) → M *ᴹ 1ᴹ ≈ᴹ M
  *ᴹ-identityʳ M = ≈ᴹ-sym (*ᴹ-identityʳ˘ M)
  open MultMult
    _≈_ 0# _+_ 0# _+_ 0# _+_ _*_ _*_ _*_ _*_ refl trans
    +-cong (+-identityˡ 0#) (sym (+-identityʳ 0#)) +-inter *-assoc
    (zero .proj₁) (distrib .proj₂)
    (λ x → sym (zero .proj₂ x)) (λ x y z → sym (distrib .proj₁ x y z)) public
    renaming (*ᴹ-*ᴹ-→ to *ᴹ-assoc)
  open ZeroMult
    0# _≈_ 0# _+_ _*_ refl trans +-cong
    (+-identityˡ 0#) annihilˡ public renaming (0ᴹ-*ᴹ to *ᴹ-annihilˡ)
  open PlusMult
    _+_ _≈_ 0# _+_ _*_ refl trans +-cong (sym (+-identityˡ 0#)) +-inter
    (λ x y z → distribˡ z x y) public renaming (+ᴹ-*ᴹ to *ᴹ-distribˡ)
  open LeftScaleMult
    _≈_ 0# _+_ 0# _+_ _*_ _*_ _*_ _*_ refl trans +-cong
    (λ x → sym (annihilʳ x)) (λ x y z → sym (distribʳ x y z)) *-assoc public
    renaming (*ₗ-*ᴹ to *ₗ-assoc-*ᴹ)
