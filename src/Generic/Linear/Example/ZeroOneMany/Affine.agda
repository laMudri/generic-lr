{-# OPTIONS --safe --without-K --postfix-projections #-}

module Generic.Linear.Example.ZeroOneMany.Affine where

  open import Algebra.Skew
  open import Data.List
  open import Data.Product
  open import Function.Base
  open import Level using (0ℓ)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

  open import Generic.Linear.Example.ZeroOneMany public using
    ( 0#1ω; 0#; 1#; ω#; _+_; _*_; +-identityʳ; +-assoc; +-comm
    ; *-identityʳ; *-assoc; annihilʳ; distribˡ; distribʳ
    )

  infix 4 _≤_

  data _≤_ : (a b : 0#1ω) → Set where
    ≤-refl : ∀ {a} → a ≤ a
    ω≤0 : ω# ≤ 0#
    ω≤1 : ω# ≤ 1#
    1≤0 : 1# ≤ 0#

  rawSkewSemiring : RawSkewSemiring 0ℓ 0ℓ
  rawSkewSemiring = record
    { rawProset = record { Carrier = 0#1ω; _≤_ = _≤_ }
    ; 0# = 0#
    ; _+_ = _+_
    ; 1# = 1#
    ; _*_ = _*_
    }

  ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans ≤-refl yz = yz
  ≤-trans ω≤0 ≤-refl = ω≤0
  ≤-trans ω≤1 ≤-refl = ω≤1
  ≤-trans ω≤1 1≤0 = ω≤0
  ≤-trans 1≤0 ≤-refl = 1≤0

  ω#≤ : ∀ {x} → ω# ≤ x
  ω#≤ {0#} = ω≤0
  ω#≤ {1#} = ω≤1
  ω#≤ {ω#} = ≤-refl
  ≤0# : ∀ {x} → x ≤ 0#
  ≤0# {0#} = ≤-refl
  ≤0# {1#} = 1≤0
  ≤0# {ω#} = ω≤0

  ≡⇒≤ : ∀ {x y} → x ≡ y → x ≤ y
  ≡⇒≤ refl = ≤-refl

  +-mono : ∀ {x x′ y y′} → x ≤ x′ → y ≤ y′ → x + y ≤ x′ + y′
  +-mono ≤-refl ≤-refl = ≤-refl
  +-mono (≤-refl {0#}) ω≤0 = ω≤0
  +-mono (≤-refl {1#}) ω≤0 = ω≤1
  +-mono (≤-refl {ω#}) ω≤0 = ≤-refl
  +-mono (≤-refl {0#}) ω≤1 = ω≤1
  +-mono (≤-refl {1#}) ω≤1 = ≤-refl
  +-mono (≤-refl {ω#}) ω≤1 = ≤-refl
  +-mono (≤-refl {0#}) 1≤0 = 1≤0
  +-mono (≤-refl {1#}) 1≤0 = ω≤1
  +-mono (≤-refl {ω#}) 1≤0 = ≤-refl
  +-mono ω≤0 yy = ω#≤
  +-mono ω≤1 yy = ω#≤
  +-mono 1≤0 (≤-refl {0#}) = 1≤0
  +-mono 1≤0 (≤-refl {1#}) = ω≤1
  +-mono 1≤0 (≤-refl {ω#}) = ≤-refl
  +-mono 1≤0 ω≤0 = ω≤0
  +-mono 1≤0 ω≤1 = ω≤1
  +-mono 1≤0 1≤0 = ω≤0

  *-mono : ∀ {x x′ y y′} → x ≤ x′ → y ≤ y′ → x * y ≤ x′ * y′
  *-mono (≤-refl {0#}) yy = ≤-refl
  *-mono (≤-refl {1#}) yy = yy
  *-mono (≤-refl {ω#}) ≤-refl = ≤-refl
  *-mono (≤-refl {ω#}) ω≤0 = ω≤0
  *-mono (≤-refl {ω#}) ω≤1 = ≤-refl
  *-mono (≤-refl {ω#}) 1≤0 = ω≤0
  *-mono ω≤0 yy = ≤0#
  *-mono ω≤1 (≤-refl {0#}) = ≤-refl
  *-mono ω≤1 (≤-refl {1#}) = ω≤1
  *-mono ω≤1 (≤-refl {ω#}) = ≤-refl
  *-mono ω≤1 ω≤0 = ω≤0
  *-mono ω≤1 ω≤1 = ω≤1
  *-mono ω≤1 1≤0 = ω≤0
  *-mono 1≤0 yy = ≤0#

  skewSemiring : SkewSemiring 0ℓ 0ℓ
  skewSemiring = record
    { proset = record
      { _≤_ = _≤_
      ; isProset = record { refl = ≤-refl ; trans = ≤-trans }
      }
    ; 0# = 0#
    ; plus = record { _∙_ = _+_ ; mono = +-mono }
    ; 1# = 1#
    ; mult = record { _∙_ = _*_ ; mono = *-mono }
    ; isSkewSemiring = record
      { +-isSkewCommutativeMonoid = record
        { isLeftSkewMonoid = record
          { identity = λ- ≤-refl , ≡⇒≤ ∘ sym ∘ +-identityʳ
          ; assoc = λ x y z → ≡⇒≤ (+-assoc x y z)
          }
        ; isRightSkewMonoid = record
          { identity = λ- ≤-refl , ≡⇒≤ ∘ +-identityʳ
          ; assoc = λ x y z → ≡⇒≤ (sym (+-assoc x y z))
          }
        ; comm = λ x y → ≡⇒≤ (+-comm x y)
        }
      ; *-isSkewMonoid = record
        { identity = λ- ≤-refl , ≡⇒≤ ∘ *-identityʳ
        ; assoc = λ x y z → ≡⇒≤ (*-assoc x y z)
        }
      ; annihil = λ- ≤-refl , ≡⇒≤ ∘ annihilʳ
      ; distrib = (λ x y z → ≡⇒≤ (distribˡ x y z))
                , (λ x y z → ≡⇒≤ (distribʳ x y z))
      }
    }
