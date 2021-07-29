{-# OPTIONS --safe --without-K --postfix-projections #-}

module Generic.Linear.Example.ZeroOneMany where

  open import Algebra.Po
  open import Algebra.Skew
  open import Data.List
  open import Data.Product
  open import Function.Base
  open import Level using (0ℓ)
  open import Relation.Binary.PropositionalEquality as ≡ using
    (_≡_; refl; trans; sym; isEquivalence)

  infix 7 _*_
  infix 6 _+_
  infix 4 _≤_

  data u01ω : Set where
    u0 u1 uω : u01ω

  data _≤_ : (a b : u01ω) → Set where
    ≤-refl : ∀ {a} → a ≤ a
    ω≤0 : uω ≤ u0
    ω≤1 : uω ≤ u1

  _+_ : (a b : u01ω) → u01ω
  u0 + b = b
  u1 + u0 = u1
  u1 + u1 = uω
  u1 + uω = uω
  uω + b = uω

  _*_ : (a b : u01ω) → u01ω
  u0 * b = u0
  u1 * b = b
  uω * u0 = u0
  uω * u1 = uω
  uω * uω = uω

  rawSkewSemiring : RawSkewSemiring 0ℓ 0ℓ
  rawSkewSemiring = record
    { rawProset = record { Carrier = u01ω; _≤_ = _≤_ }
    ; 0# = u0
    ; _+_ = _+_
    ; 1# = u1
    ; _*_ = _*_
    }

  rawPoSemiring : RawPoSemiring 0ℓ 0ℓ 0ℓ
  rawPoSemiring = record
    { rawPoset = record { Carrier = u01ω ; _≈_ = _≡_ ; _≤_ = _≤_ }
    ; RawSkewSemiring rawSkewSemiring
    }

  ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans ≤-refl yz = yz
  ≤-trans ω≤0 ≤-refl = ω≤0
  ≤-trans ω≤1 ≤-refl = ω≤1

  uω≤ : ∀ {x} → uω ≤ x
  uω≤ {u0} = ω≤0
  uω≤ {u1} = ω≤1
  uω≤ {uω} = ≤-refl

  +-mono : ∀ {x x′ y y′} → x ≤ x′ → y ≤ y′ → x + y ≤ x′ + y′
  +-mono ≤-refl ≤-refl = ≤-refl
  +-mono {x = u0} ≤-refl ω≤0 = ω≤0
  +-mono {x = u1} ≤-refl ω≤0 = ω≤1
  +-mono {x = uω} ≤-refl ω≤0 = ≤-refl
  +-mono {x = u0} ≤-refl ω≤1 = ω≤1
  +-mono {x = u1} ≤-refl ω≤1 = ≤-refl
  +-mono {x = uω} ≤-refl ω≤1 = ≤-refl
  +-mono ω≤0 ≤-refl = uω≤
  +-mono ω≤0 ω≤0 = ω≤0
  +-mono ω≤0 ω≤1 = ω≤1
  +-mono ω≤1 ≤-refl = uω≤
  +-mono ω≤1 ω≤0 = ω≤1
  +-mono ω≤1 ω≤1 = ≤-refl

  *-mono : ∀ {x x′ y y′} → x ≤ x′ → y ≤ y′ → x * y ≤ x′ * y′
  *-mono ≤-refl ≤-refl = ≤-refl
  *-mono {x = u0} ≤-refl ω≤0 = ≤-refl
  *-mono {x = u1} ≤-refl ω≤0 = ω≤0
  *-mono {x = uω} ≤-refl ω≤0 = ω≤0
  *-mono {x = u0} ≤-refl ω≤1 = ≤-refl
  *-mono {x = u1} ≤-refl ω≤1 = ω≤1
  *-mono {x = uω} ≤-refl ω≤1 = ≤-refl
  *-mono {y = u0} ω≤0 yy = ≤-refl
  *-mono {y = u1} ω≤0 yy = ω≤0
  *-mono {y = uω} ω≤0 yy = ω≤0
  *-mono {y = u0} ω≤1 yy = yy
  *-mono {y = u1} ω≤1 yy = uω≤
  *-mono {y = uω} ω≤1 yy = uω≤

  ≡⇒≤ : ∀ {x y} → x ≡ y → x ≤ y
  ≡⇒≤ refl = ≤-refl

  +-identityʳ : ∀ x → x + u0 ≡ x
  +-identityʳ u0 = refl
  +-identityʳ u1 = refl
  +-identityʳ uω = refl

  +-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
  +-assoc u0 y z = refl
  +-assoc u1 u0 z = refl
  +-assoc u1 u1 u0 = refl
  +-assoc u1 u1 u1 = refl
  +-assoc u1 u1 uω = refl
  +-assoc u1 uω z = refl
  +-assoc uω y z = refl

  +-comm : ∀ x y → x + y ≡ y + x
  +-comm u0 u0 = refl
  +-comm u0 u1 = refl
  +-comm u0 uω = refl
  +-comm u1 u0 = refl
  +-comm u1 u1 = refl
  +-comm u1 uω = refl
  +-comm uω u0 = refl
  +-comm uω u1 = refl
  +-comm uω uω = refl

  *-identityʳ : ∀ x → x ≡ x * u1
  *-identityʳ u0 = refl
  *-identityʳ u1 = refl
  *-identityʳ uω = refl

  *-assoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
  *-assoc u0 y z = refl
  *-assoc u1 y z = refl
  *-assoc uω u0 z = refl
  *-assoc uω u1 z = refl
  *-assoc uω uω u0 = refl
  *-assoc uω uω u1 = refl
  *-assoc uω uω uω = refl

  annihilʳ : ∀ x → u0 ≡ x * u0
  annihilʳ u0 = refl
  annihilʳ u1 = refl
  annihilʳ uω = refl

  distribˡ : ∀ x y z → (x + y) * z ≡ x * z + y * z
  distribˡ u0 y z = refl
  distribˡ u1 u0 u0 = refl
  distribˡ u1 u0 u1 = refl
  distribˡ u1 u0 uω = refl
  distribˡ u1 u1 u0 = refl
  distribˡ u1 u1 u1 = refl
  distribˡ u1 u1 uω = refl
  distribˡ u1 uω u0 = refl
  distribˡ u1 uω u1 = refl
  distribˡ u1 uω uω = refl
  distribˡ uω u0 u0 = refl
  distribˡ uω u1 u0 = refl
  distribˡ uω uω u0 = refl
  distribˡ uω y u1 = refl
  distribˡ uω y uω = refl

  distribʳ : ∀ x y z → x * y + x * z ≡ x * (y + z)
  distribʳ u0 y z = refl
  distribʳ u1 y z = refl
  distribʳ uω u0 z = refl
  distribʳ uω u1 u0 = refl
  distribʳ uω u1 u1 = refl
  distribʳ uω u1 uω = refl
  distribʳ uω uω z = refl

  antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
  antisym ≤-refl yx = refl
  antisym ω≤0 ()
  antisym ω≤1 ()

  poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ
  poSemiring = record
    { RawPoSemiring rawPoSemiring
    ; isPoSemiring = record
      { isPartialOrder = record
        { isPreorder = record
          { isEquivalence = isEquivalence
          ; reflexive = ≡⇒≤
          ; trans = ≤-trans
          }
        ; antisym = antisym
        }
      ; isSemiring = record
        { isSemiringWithoutAnnihilatingZero = record
          { +-isCommutativeMonoid = record
            { isMonoid = record
              { isSemigroup = record
                { isMagma = record
                  { isEquivalence = isEquivalence
                  ; ∙-cong = ≡.cong₂ _
                  }
                ; assoc = +-assoc
                }
              ; identity = λ- refl , +-identityʳ
              }
            ; comm = +-comm
            }
          ; *-isMonoid = record
            { isSemigroup = record
              { isMagma = record
                { isEquivalence = isEquivalence
                ; ∙-cong = ≡.cong₂ _
                }
              ; assoc = *-assoc
              }
            ; identity = λ- refl , sym ∘ *-identityʳ
            }
          ; distrib = (λ x y z → sym (distribʳ x y z))
                    , (λ x y z → distribˡ y z x)
          }
        ; zero = λ- refl , sym ∘ annihilʳ
        }
      ; +-mono = +-mono
      ; *-mono = *-mono
      }
    }

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

  u0⁻¹ : ∀ x → List (x ≤ u0)
  u0⁻¹ u0 = ≤-refl ∷ []
  u0⁻¹ u1 = []
  u0⁻¹ uω = ω≤0 ∷ []

  +⁻¹ : ∀ x → List (∃ \ ((y , z) : _ × _) → x ≤ y + z)
  +⁻¹ u0 = ((u0 , u0) , ≤-refl) ∷ []
  +⁻¹ u1 = ((u1 , u0) , ≤-refl) ∷ ((u0 , u1) , ≤-refl) ∷ []
  +⁻¹ uω = ((uω , uω) , ≤-refl) ∷ []

  u1⁻¹ : ∀ x → List (x ≤ u1)
  u1⁻¹ u0 = []
  u1⁻¹ u1 = ≤-refl ∷ []
  u1⁻¹ uω = ω≤1 ∷ []

  *⁻¹ : ∀ x z → List (∃ \ y → z ≤ x * y)
  *⁻¹ u0 u0 = (uω , ≤-refl) ∷ []
  *⁻¹ u0 u1 = []
  *⁻¹ u0 uω = []
  *⁻¹ u1 z = (z , ≤-refl) ∷ []
  *⁻¹ uω u0 = (u0 , ≤-refl) ∷ []
  *⁻¹ uω u1 = []
  *⁻¹ uω uω = (uω , ≤-refl) ∷ []

  rep : ∀ x → List (∃ \ y → x ≤ y × y ≤ u0 × y ≤ y + y)
  rep u0 = (u0 , ≤-refl , ≤-refl , ≤-refl) ∷ []
  rep u1 = []
  rep uω = (uω , ≤-refl , ω≤0 , ≤-refl) ∷ []

  ω*-del : ∀ x → uω * x ≤ u0
  ω*-del u0 = ≤-refl
  ω*-del u1 = ω≤0
  ω*-del uω = ω≤0

  ω*-dup : ∀ x → uω * x ≤ uω * x + uω * x
  ω*-dup u0 = ≤-refl
  ω*-dup u1 = ≤-refl
  ω*-dup uω = ≤-refl

  ω*-≤ : ∀ x → uω * x ≤ x
  ω*-≤ u0 = ≤-refl
  ω*-≤ u1 = ω≤1
  ω*-≤ uω = ≤-refl
