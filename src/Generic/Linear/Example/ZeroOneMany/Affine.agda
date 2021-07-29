{-# OPTIONS --safe --without-K --postfix-projections #-}

module Generic.Linear.Example.ZeroOneMany.Affine where

  open import Algebra.Skew
  open import Data.List
  open import Data.Product
  open import Function.Base
  open import Level using (0ℓ)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

  open import Generic.Linear.Example.ZeroOneMany public using
    ( u01ω; u0; u1; uω; _+_; _*_; +-identityʳ; +-assoc; +-comm
    ; *-identityʳ; *-assoc; annihilʳ; distribˡ; distribʳ
    )

  infix 4 _≤_

  data _≤_ : (a b : u01ω) → Set where
    ≤-refl : ∀ {a} → a ≤ a
    ω≤0 : uω ≤ u0
    ω≤1 : uω ≤ u1
    1≤0 : u1 ≤ u0

  rawSkewSemiring : RawSkewSemiring 0ℓ 0ℓ
  rawSkewSemiring = record
    { rawProset = record { Carrier = u01ω; _≤_ = _≤_ }
    ; 0# = u0
    ; _+_ = _+_
    ; 1# = u1
    ; _*_ = _*_
    }

  ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans ≤-refl yz = yz
  ≤-trans ω≤0 ≤-refl = ω≤0
  ≤-trans ω≤1 ≤-refl = ω≤1
  ≤-trans ω≤1 1≤0 = ω≤0
  ≤-trans 1≤0 ≤-refl = 1≤0

  uω≤ : ∀ {x} → uω ≤ x
  uω≤ {u0} = ω≤0
  uω≤ {u1} = ω≤1
  uω≤ {uω} = ≤-refl
  ≤u0 : ∀ {x} → x ≤ u0
  ≤u0 {u0} = ≤-refl
  ≤u0 {u1} = 1≤0
  ≤u0 {uω} = ω≤0

  ≡⇒≤ : ∀ {x y} → x ≡ y → x ≤ y
  ≡⇒≤ refl = ≤-refl

  +-mono : ∀ {x x′ y y′} → x ≤ x′ → y ≤ y′ → x + y ≤ x′ + y′
  +-mono ≤-refl ≤-refl = ≤-refl
  +-mono (≤-refl {u0}) ω≤0 = ω≤0
  +-mono (≤-refl {u1}) ω≤0 = ω≤1
  +-mono (≤-refl {uω}) ω≤0 = ≤-refl
  +-mono (≤-refl {u0}) ω≤1 = ω≤1
  +-mono (≤-refl {u1}) ω≤1 = ≤-refl
  +-mono (≤-refl {uω}) ω≤1 = ≤-refl
  +-mono (≤-refl {u0}) 1≤0 = 1≤0
  +-mono (≤-refl {u1}) 1≤0 = ω≤1
  +-mono (≤-refl {uω}) 1≤0 = ≤-refl
  +-mono ω≤0 yy = uω≤
  +-mono ω≤1 yy = uω≤
  +-mono 1≤0 (≤-refl {u0}) = 1≤0
  +-mono 1≤0 (≤-refl {u1}) = ω≤1
  +-mono 1≤0 (≤-refl {uω}) = ≤-refl
  +-mono 1≤0 ω≤0 = ω≤0
  +-mono 1≤0 ω≤1 = ω≤1
  +-mono 1≤0 1≤0 = ω≤0

  *-mono : ∀ {x x′ y y′} → x ≤ x′ → y ≤ y′ → x * y ≤ x′ * y′
  *-mono (≤-refl {u0}) yy = ≤-refl
  *-mono (≤-refl {u1}) yy = yy
  *-mono (≤-refl {uω}) ≤-refl = ≤-refl
  *-mono (≤-refl {uω}) ω≤0 = ω≤0
  *-mono (≤-refl {uω}) ω≤1 = ≤-refl
  *-mono (≤-refl {uω}) 1≤0 = ω≤0
  *-mono ω≤0 yy = ≤u0
  *-mono ω≤1 (≤-refl {u0}) = ≤-refl
  *-mono ω≤1 (≤-refl {u1}) = ω≤1
  *-mono ω≤1 (≤-refl {uω}) = ≤-refl
  *-mono ω≤1 ω≤0 = ω≤0
  *-mono ω≤1 ω≤1 = ω≤1
  *-mono ω≤1 1≤0 = ω≤0
  *-mono 1≤0 yy = ≤u0

  skewSemiring : SkewSemiring 0ℓ 0ℓ
  skewSemiring = record
    { proset = record
      { _≤_ = _≤_
      ; isProset = record { refl = ≤-refl ; trans = ≤-trans }
      }
    ; 0# = u0
    ; plus = record { _∙_ = _+_ ; mono = +-mono }
    ; 1# = u1
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
