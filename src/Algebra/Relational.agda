{-# OPTIONS --without-K --safe --postfix-projections #-}

-- I think the requirements for propositional equalities make these definitions
-- less general than they could be, though they only affect identity cases,
-- which *tend* to hold up to propositional equality anyway.
-- Motivating example: (Bag A, ⟅⟆, _+_)

module Algebra.Relational where

  -- open import Function.Base using (flip)
  open import Level
  open import Relation.Binary using (REL)
  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary

  infix 3 _◇_
  infixr 4 _,_ _↘,_,↙_

  record _◇_ {a p q} {A : Set a} (P : Pred A p) (Q : Pred A q)
             : Set (a ⊔ p ⊔ q) where
    constructor _,_
    field
      {middle} : A
      fst : P middle
      snd : Q middle
  open _◇_ public

  record _↘_↙_ {a b p q r} {A : Set a} {B : Set b}
               (P : Pred A p) (R : REL A B r) (Q : Pred B q)
               : Set (a ⊔ b ⊔ p ⊔ q ⊔ r) where
    constructor _↘,_,↙_
    field
      {left} : A
      {right} : B
      lprf : P left
      centre : R left right
      rprf : Q right

  record RawRelMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      Carrier : Set c
      _≤ε : Carrier → Set ℓ
      _≤[_∙_] : (x y z : Carrier) → Set ℓ

  record IsLeftSkewRelMonoid
    {c ℓ} {C : Set c} (_≤ε : C → Set ℓ) (_≤[_∙_] : C → C → C → Set ℓ)
    : Set (c ⊔ ℓ) where
    field
      identityˡ→ : ∀ {y z} → _≤ε ◇ z ≤[_∙ y ] → y ≡ z
      identityʳ← : ∀ {x z} → x ≡ z → z ≤[ x ∙_] ◇ _≤ε
      assoc→ : ∀ {w x y z} → _≤[ w ∙ x ] ◇ z ≤[_∙ y ] → z ≤[ w ∙_] ◇ _≤[ x ∙ y ]

  record IsRightSkewRelMonoid
    {c ℓ} {C : Set c} (_≤ε : C → Set ℓ) (_≤[_∙_] : C → C → C → Set ℓ)
    : Set (c ⊔ ℓ) where
    field
      identityˡ← : ∀ {y z} → y ≡ z → _≤ε ◇ z ≤[_∙ y ]
      identityʳ→ : ∀ {x z} → z ≤[ x ∙_] ◇ _≤ε → x ≡ z
      assoc← : ∀ {w x y z} → z ≤[ w ∙_] ◇ _≤[ x ∙ y ] → _≤[ w ∙ x ] ◇ z ≤[_∙ y ]

  record IsSkewCommutativeRelMonoid
    {c ℓ} {C : Set c} (_≤ε : C → Set ℓ) (_≤[_∙_] : C → C → C → Set ℓ)
    : Set (c ⊔ ℓ) where
    field
      isLeftSkewRelMonoid : IsLeftSkewRelMonoid _≤ε _≤[_∙_]
      isRightSkewRelMonoid : IsRightSkewRelMonoid _≤ε _≤[_∙_]
      comm : ∀ {x y z} → x ≤[ y ∙ z ] → x ≤[ z ∙ y ]
    open IsLeftSkewRelMonoid isLeftSkewRelMonoid public
    open IsRightSkewRelMonoid isRightSkewRelMonoid public

  record LeftSkewRelMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      Carrier : Set c
      _≤ε : Carrier → Set ℓ
      _≤[_∙_] : (x y z : Carrier) → Set ℓ
      isLeftSkewRelMonoid : IsLeftSkewRelMonoid _≤ε _≤[_∙_]
    open IsLeftSkewRelMonoid isLeftSkewRelMonoid public

  record RightSkewRelMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      Carrier : Set c
      _≤ε : Carrier → Set ℓ
      _≤[_∙_] : (x y z : Carrier) → Set ℓ
      isRightSkewRelMonoid : IsRightSkewRelMonoid _≤ε _≤[_∙_]
    open IsRightSkewRelMonoid isRightSkewRelMonoid public

  record SkewCommutativeRelMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      Carrier : Set c
      _≤ε : Carrier → Set ℓ
      _≤[_∙_] : (x y z : Carrier) → Set ℓ
      isSkewCommutativeRelMonoid : IsSkewCommutativeRelMonoid _≤ε _≤[_∙_]
    open IsSkewCommutativeRelMonoid isSkewCommutativeRelMonoid public

    leftSkewRelMonoid : LeftSkewRelMonoid c ℓ
    leftSkewRelMonoid = record { isLeftSkewRelMonoid = isLeftSkewRelMonoid }
    rightSkewRelMonoid : RightSkewRelMonoid c ℓ
    rightSkewRelMonoid = record { isRightSkewRelMonoid = isRightSkewRelMonoid }

    inter : ∀ {v w x y z} →
            _≤[ v ∙ w ] ↘ z ≤[_∙_] ↙ _≤[ x ∙ y ] →
            _≤[ v ∙ x ] ↘ z ≤[_∙_] ↙ _≤[ w ∙ y ]
    inter (vw≤v∙w ↘, z≤vw∙xy ,↙ xy≤x∙y) =
      let z≤v∙wxy , wxy≤w∙xy = assoc→ (vw≤v∙w , z≤vw∙xy) in
      let wx≤w∙x , wxy≤wx∙y = assoc← (wxy≤w∙xy , xy≤x∙y) in
      let wx≤x∙w = comm wx≤w∙x in
      let wxy≤x∙wy , wy≤w∙y = assoc→ (wx≤x∙w , wxy≤wx∙y) in
      let vx≤v∙x , z≤vx∙wy = assoc← (z≤v∙wxy , wxy≤x∙wy) in
      vx≤v∙x ↘, z≤vx∙wy ,↙ wy≤w∙y

  skewCommutativeRelMonoidˡ :
    ∀ {c ℓ} (M : LeftSkewRelMonoid c ℓ) (open LeftSkewRelMonoid M) →
    (∀ {x y z} → x ≤[ y ∙ z ] → x ≤[ z ∙ y ]) → SkewCommutativeRelMonoid c ℓ
  skewCommutativeRelMonoidˡ M comm = record
    { LeftSkewRelMonoid M
    ; isSkewCommutativeRelMonoid = record
      { isLeftSkewRelMonoid = isLeftSkewRelMonoid
      ; isRightSkewRelMonoid = record
        { identityˡ← = λ q →
          let z≤y∙x , y≤ε = identityʳ← q in y≤ε , comm z≤y∙x
        ; identityʳ→ = λ (z≤y∙x , x≤ε) → identityˡ→ (x≤ε , comm z≤y∙x)
        ; assoc← = λ (z≤y∙xw , xw≤x∙w) →
          let z≤w∙xy , xy≤x∙y = assoc→ (comm xw≤x∙w , comm z≤y∙xw) in
          comm xy≤x∙y , comm z≤w∙xy
        }
      ; comm = comm
      }
    } where open LeftSkewRelMonoid M
