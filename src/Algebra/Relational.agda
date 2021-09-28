{-# OPTIONS --without-K --safe --postfix-projections #-}

module Algebra.Relational where

  open import Algebra.Skew
  open import Data.Product
  open import Data.Unit using (⊤; tt)
  open import Function.Base using (flip; _∘_)
  open import Level
  open import Relation.Binary using (REL; Rel)
  open import Relation.Unary

  infix 3 _◇_ _↘_↙_
  infixr 4 _,_ _↘,_,↙_

  record _◇_ {a p q} {A : Set a} (P : Pred A p) (Q : Pred A q)
             : Set (a ⊔ p ⊔ q) where
    constructor _,_
    field
      {middle} : A
      fst : P middle
      snd : Q middle
  open _◇_ public

  swap-◇ : ∀ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q} → P ◇ Q → Q ◇ P
  swap-◇ (p , q) = q , p

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

  {-
  R   S
  |\ /|
  | X |
  |/ \|
  T   U
  -}
  record 2×2 {a b c d r s t u} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
    (R : REL A B r) (S : REL C D s) (T : REL A C t) (U : REL B D u)
    : Set (a ⊔ b ⊔ c ⊔ d ⊔ r ⊔ s ⊔ t ⊔ u) where
    constructor four
    field
      {rt} : A
      {ru} : B
      {st} : C
      {su} : D
      rel-↖ : R rt ru
      rel-↗ : S st su
      rel-↙ : T rt st
      rel-↘ : U ru su
  open 2×2 public using (rel-↖; rel-↗; rel-↙; rel-↘)

  record RawRelMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      Carrier : Set c
      _≤ε : Carrier → Set ℓ
      _≤[_∙_] : (x y z : Carrier) → Set ℓ

  -- Definitions

  Monotonic₁₋₀ : ∀ {c ℓ} {C : Set c} → Rel C ℓ → (C → Set ℓ) → Set _
  Monotonic₁₋₀ _≤_ _≤ε = ∀ {x x′} → x′ ≤ x → x ≤ε → x′ ≤ε

  Monotonic₁₋₂ : ∀ {c ℓ} {C : Set c} → Rel C ℓ → (C → C → C → Set ℓ) → Set _
  Monotonic₁₋₂ _≤_ _≤[_∙_] = ∀ {x x′ y y′ z z′} →
    x′ ≤ x → y ≤ y′ → z ≤ z′ →
    x ≤[ y ∙ z ] → x′ ≤[ y′ ∙ z′ ]

  Monotonic₀₋₁ : ∀ {c ℓ} {C : Set c} → Rel C ℓ → (C → Set ℓ) → Set _
  Monotonic₀₋₁ _≤_ η≤_ = Monotonic₁₋₀ (flip _≤_) η≤_

  Monotonic₂₋₁ : ∀ {c ℓ} {C : Set c} → Rel C ℓ → (C → C → C → Set ℓ) → Set _
  Monotonic₂₋₁ _≤_ [_∘_]≤_ = Monotonic₁₋₂ (flip _≤_) (λ x y z → [ y ∘ z ]≤ x)

  record Universally≤ {c ℓ p} {C : Set c} (_≤_ : Rel C ℓ) (P : Pred C p)
         : Set (c ⊔ ℓ ⊔ p) where
    constructor _,_
    field
      {witness} : C
      holds : P witness
      unique : ∀ {z} → P z → z ≤ witness
  open Universally≤ public

  Universally≥ : ∀ {c ℓ p} {C : Set c} → Rel C ℓ → Pred C p → Set (c ⊔ ℓ ⊔ p)
  Universally≥ = Universally≤ ∘ flip

  -- Structures

  record IsLeftSkewRelMonoid
    {c ℓ} {C : Set c} (_≤_ : Rel C ℓ) (_≤ε : C → Set ℓ)
    (_≤[_∙_] : C → C → C → Set ℓ) : Set (c ⊔ ℓ) where
    field
      identityˡ→ : ∀ {y z} → _≤ε ◇ z ≤[_∙ y ] → z ≤ y
      identityʳ← : ∀ {x z} → z ≤ x → z ≤[ x ∙_] ◇ _≤ε
      assoc→ : ∀ {w x y z} → _≤[ w ∙ x ] ◇ z ≤[_∙ y ] → z ≤[ w ∙_] ◇ _≤[ x ∙ y ]

  record IsRightSkewRelMonoid
    {c ℓ} {C : Set c} (_≤_ : Rel C ℓ) (_≤ε : C → Set ℓ)
    (_≤[_∙_] : C → C → C → Set ℓ) : Set (c ⊔ ℓ) where
    field
      identityˡ← : ∀ {y z} → z ≤ y → _≤ε ◇ z ≤[_∙ y ]
      identityʳ→ : ∀ {x z} → z ≤[ x ∙_] ◇ _≤ε → z ≤ x
      assoc← : ∀ {w x y z} → z ≤[ w ∙_] ◇ _≤[ x ∙ y ] → _≤[ w ∙ x ] ◇ z ≤[_∙ y ]

  record IsRelMonoid
    {c ℓ} {C : Set c} (_≤_ : Rel C ℓ) (_≤ε : C → Set ℓ)
    (_≤[_∙_] : C → C → C → Set ℓ) : Set (c ⊔ ℓ) where
    field
      isLeftSkewRelMonoid : IsLeftSkewRelMonoid _≤_ _≤ε _≤[_∙_]
      isRightSkewRelMonoid : IsRightSkewRelMonoid _≤_ _≤ε _≤[_∙_]
    open IsLeftSkewRelMonoid isLeftSkewRelMonoid public
    open IsRightSkewRelMonoid isRightSkewRelMonoid public

  record IsCommutativeRelMonoid
    {c ℓ} {C : Set c} (_≤_ : Rel C ℓ) (_≤ε : C → Set ℓ)
    (_≤[_∙_] : C → C → C → Set ℓ) : Set (c ⊔ ℓ) where
    field
      isRelMonoid : IsRelMonoid _≤_ _≤ε _≤[_∙_]
      comm : ∀ {x y z} → x ≤[ y ∙ z ] → x ≤[ z ∙ y ]
    open IsRelMonoid isRelMonoid public

  IsRelComonoid :
    ∀ {c ℓ} {C : Set c} (_≤_ : Rel C ℓ) (η≤_ : C → Set ℓ)
    ([_∘_]≤_ : C → C → C → Set ℓ) → Set (c ⊔ ℓ)
  IsRelComonoid _≤_ η≤_ [_∘_]≤_ =
    IsRelMonoid (flip _≤_) η≤_ (λ z x y → [ x ∘ y ]≤ z)

  IsCommutativeRelComonoid :
    ∀ {c ℓ} {C : Set c} (_≤_ : Rel C ℓ) (η≤_ : C → Set ℓ)
    ([_∘_]≤_ : C → C → C → Set ℓ) → Set (c ⊔ ℓ)
  IsCommutativeRelComonoid _≤_ η≤_ [_∘_]≤_ =
    IsCommutativeRelMonoid (flip _≤_) η≤_ (λ z x y → [ x ∘ y ]≤ z)

  record IsBicommutativeBimonoid
    {c ℓ} {C : Set c} (_≤_ : Rel C ℓ)
    (η≤_ : C → Set ℓ) ([_∘_]≤_ : C → C → C → Set ℓ)
    (_≤ε : C → Set ℓ) (_≤[_∙_] : C → C → C → Set ℓ)
    : Set (c ⊔ ℓ) where
    field
      isCommutativeRelComonoid : IsCommutativeRelComonoid _≤_ η≤_ [_∘_]≤_
      isCommutativeRelMonoid : IsCommutativeRelMonoid _≤_ _≤ε _≤[_∙_]
      η-ε→ : η≤_ ◇ _≤ε → ⊤
      η-ε← : ⊤ → η≤_ ◇ _≤ε
      η-∙→ : ∀ {x y} → η≤_ ◇ _≤[ x ∙ y ] → η≤ x × η≤ y
      η-∙← : ∀ {x y} → η≤ x × η≤ y → η≤_ ◇ _≤[ x ∙ y ]
      ∘-ε→ : ∀ {x y} → [ x ∘ y ]≤_ ◇ _≤ε → x ≤ε × y ≤ε
      ∘-ε← : ∀ {x y} → x ≤ε × y ≤ε → [ x ∘ y ]≤_ ◇ _≤ε
      ∘-∙→ : ∀ {w x y z} →
        [ w ∘ x ]≤_ ◇ _≤[ y ∙ z ] →
        2×2 (w ≤[_∙_]) (x ≤[_∙_]) ([_∘_]≤ y) ([_∘_]≤ z)
      ∘-∙← : ∀ {w x y z} →
        2×2 (w ≤[_∙_]) (x ≤[_∙_]) ([_∘_]≤ y) ([_∘_]≤ z) →
        [ w ∘ x ]≤_ ◇ _≤[ y ∙ z ]
    open IsCommutativeRelMonoid isCommutativeRelComonoid public renaming
      ( identityˡ→ to ∘-identityˡ→; identityˡ← to ∘-identityˡ←
      ; identityʳ→ to ∘-identityʳ→; identityʳ← to ∘-identityʳ←
      ; assoc→ to ∘-assoc→; assoc← to ∘-assoc←; comm to ∘-comm
      ; isLeftSkewRelMonoid to ∘-isLeftSkewRelComonoid
      ; isRightSkewRelMonoid to ∘-isRightSkewRelComonoid
      ; isRelMonoid to ∘-isRelComonoid
      )
    open IsCommutativeRelMonoid isCommutativeRelMonoid public renaming
      ( identityˡ→ to ∙-identityˡ→; identityˡ← to ∙-identityˡ←
      ; identityʳ→ to ∙-identityʳ→; identityʳ← to ∙-identityʳ←
      ; assoc→ to ∙-assoc→; assoc← to ∙-assoc←; comm to ∙-comm
      ; isLeftSkewRelMonoid to ∙-isLeftSkewRelMonoid
      ; isRightSkewRelMonoid to ∙-isRightSkewRelMonoid
      ; isRelMonoid to ∙-isRelMonoid
      )

  record IsRelSemiring
    {c ℓ} {C : Set c} (_≤_ : Rel C ℓ)
    (_≤0 : C → Set ℓ) (_≤[_+_] : C → C → C → Set ℓ)
    (_≤1 : C → Set ℓ) (_≤[_*_] : C → C → C → Set ℓ)
    : Set (c ⊔ ℓ) where
    field
      +-isCommutativeRelMonoid : IsCommutativeRelMonoid _≤_ _≤0 _≤[_+_]
      *-isRelMonoid : IsRelMonoid _≤_ _≤1 _≤[_*_]
      annihilˡ→ : ∀ {y z} → _≤0 ◇ z ≤[_* y ] → z ≤0
      annihilˡ← : ∀ {y z} → z ≤0 → _≤0 ◇ z ≤[_* y ]
      annihilʳ→ : ∀ {x z} → z ≤[ x *_] ◇ _≤0 → z ≤0
      annihilʳ← : ∀ {x z} → z ≤0 → z ≤[ x *_] ◇ _≤0
      distribˡ→ : ∀ {w x y z} →
        _≤[ w + x ] ◇ z ≤[_* y ] → _≤[ w * y ] ↘ z ≤[_+_] ↙ _≤[ x * y ]
      distribˡ← : ∀ {w x y z} →
        _≤[ w * y ] ↘ z ≤[_+_] ↙ _≤[ x * y ] → _≤[ w + x ] ◇ z ≤[_* y ]
      distribʳ→ : ∀ {w x y z} →
        z ≤[ w *_] ◇ _≤[ x + y ] → _≤[ w * x ] ↘ z ≤[_+_] ↙ _≤[ w * y ]
      distribʳ← : ∀ {w x y z} →
        _≤[ w * x ] ↘ z ≤[_+_] ↙ _≤[ w * y ] → z ≤[ w *_] ◇ _≤[ x + y ]

    open IsCommutativeRelMonoid +-isCommutativeRelMonoid public
      using () renaming
      ( identityˡ→ to +-identityˡ→; identityˡ← to +-identityˡ←
      ; identityʳ→ to +-identityʳ→; identityʳ← to +-identityʳ←
      ; assoc→ to +-assoc→; assoc← to +-assoc←
      ; comm to +-comm
      ; isLeftSkewRelMonoid to +-isLeftSkewRelMonoid
      ; isRightSkewRelMonoid to +-isRightSkewRelMonoid
      ; isRelMonoid to +-isRelMonoid
      )
    open IsRelMonoid *-isRelMonoid public using () renaming
      ( identityˡ→ to *-identityˡ→; identityˡ← to *-identityˡ←
      ; identityʳ→ to *-identityʳ→; identityʳ← to *-identityʳ←
      ; assoc→ to *-assoc→; assoc← to *-assoc←
      ; isLeftSkewRelMonoid to *-isLeftSkewRelMonoid
      ; isRightSkewRelMonoid to *-isRightSkewRelMonoid
      )

  record IsFRelSemiring
    {c ℓ} {C : Set c} (_≤_ : Rel C ℓ)
    (_≤0 : C → Set ℓ) (_≤[_+_] : C → C → C → Set ℓ)
    (_≤1 : C → Set ℓ) (_≤[_*_] : C → C → C → Set ℓ)
    : Set (c ⊔ ℓ) where
    field
      isRelSemiring : IsRelSemiring _≤_ _≤0 _≤[_+_] _≤1 _≤[_*_]
      0-func : Universally≤ _≤_ _≤0
      +-func : ∀ x y → Universally≤ _≤_ _≤[ x + y ]
      1-func : Universally≤ _≤_ _≤1
      *-func : ∀ x y → Universally≤ _≤_ _≤[ x * y ]

    open IsRelSemiring isRelSemiring public

  -- Bundles

  record LeftSkewRelMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      Carrier : Set c
      _≤_ : Rel Carrier ℓ
      _≤ε : Carrier → Set ℓ
      _≤[_∙_] : (x y z : Carrier) → Set ℓ
      isProset : IsProset _≤_
      ε-mono : Monotonic₁₋₀ _≤_ _≤ε
      ∙-mono : Monotonic₁₋₂ _≤_ _≤[_∙_]
      isLeftSkewRelMonoid : IsLeftSkewRelMonoid _≤_ _≤ε _≤[_∙_]
    open IsProset isProset public
    open IsLeftSkewRelMonoid isLeftSkewRelMonoid public

  record RightSkewRelMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      Carrier : Set c
      _≤_ : Rel Carrier ℓ
      _≤ε : Carrier → Set ℓ
      _≤[_∙_] : (x y z : Carrier) → Set ℓ
      isProset : IsProset _≤_
      ε-mono : Monotonic₁₋₀ _≤_ _≤ε
      ∙-mono : Monotonic₁₋₂ _≤_ _≤[_∙_]
      isRightSkewRelMonoid : IsRightSkewRelMonoid _≤_ _≤ε _≤[_∙_]
    open IsProset isProset public
    open IsRightSkewRelMonoid isRightSkewRelMonoid public

  record RelMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      Carrier : Set c
      _≤_ : Rel Carrier ℓ
      _≤ε : Carrier → Set ℓ
      _≤[_∙_] : (x y z : Carrier) → Set ℓ
      isProset : IsProset _≤_
      ε-mono : Monotonic₁₋₀ _≤_ _≤ε
      ∙-mono : Monotonic₁₋₂ _≤_ _≤[_∙_]
      isRelMonoid : IsRelMonoid _≤_ _≤ε _≤[_∙_]
    open IsProset isProset public
    open IsRelMonoid isRelMonoid public

    proset : Proset c ℓ
    proset = record { isProset = isProset }
    open Proset proset public using (rawProset)
    leftSkewRelMonoid : LeftSkewRelMonoid c ℓ
    leftSkewRelMonoid = record
      { isProset = isProset; ε-mono = ε-mono; ∙-mono = ∙-mono
      ; isLeftSkewRelMonoid = isLeftSkewRelMonoid
      }
    rightSkewRelMonoid : RightSkewRelMonoid c ℓ
    rightSkewRelMonoid = record
      { isProset = isProset; ε-mono = ε-mono; ∙-mono = ∙-mono
      ; isRightSkewRelMonoid = isRightSkewRelMonoid
      }

    identity²→ : ∀ {z} → _≤ε ↘ z ≤[_∙_] ↙ _≤ε → z ≤ε
    identity²→ (x0 ↘, z+ ,↙ y0) = ε-mono (identityˡ→ (x0 , z+)) y0
    identity²← : ∀ {z} → z ≤ε → _≤ε ↘ z ≤[_∙_] ↙ _≤ε
    identity²← z0 =
      let z+ , y0 = identityʳ← refl in
      z0 ↘, z+ ,↙ y0

  record CommutativeRelMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      Carrier : Set c
      _≤_ : Rel Carrier ℓ
      _≤ε : Carrier → Set ℓ
      _≤[_∙_] : (x y z : Carrier) → Set ℓ
      isProset : IsProset _≤_
      ε-mono : Monotonic₁₋₀ _≤_ _≤ε
      ∙-mono : Monotonic₁₋₂ _≤_ _≤[_∙_]
      isCommutativeRelMonoid : IsCommutativeRelMonoid _≤_ _≤ε _≤[_∙_]
    open IsProset isProset public
    open IsCommutativeRelMonoid isCommutativeRelMonoid public

    relMonoid : RelMonoid c ℓ
    relMonoid = record
      { isProset = isProset; ε-mono = ε-mono; ∙-mono = ∙-mono
      ; isRelMonoid = isRelMonoid
      }
    open RelMonoid relMonoid public using
      (proset; leftSkewRelMonoid; rightSkewRelMonoid; identity²→; identity²←)

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

  commutativeRelMonoidˡ :
    ∀ {c ℓ} (M : LeftSkewRelMonoid c ℓ) (open LeftSkewRelMonoid M) →
    (∀ {x y z} → x ≤[ y ∙ z ] → x ≤[ z ∙ y ]) → CommutativeRelMonoid c ℓ
  commutativeRelMonoidˡ M comm = record
    { LeftSkewRelMonoid M
    ; isCommutativeRelMonoid = record
      { isRelMonoid = record
        { isLeftSkewRelMonoid = isLeftSkewRelMonoid
        ; isRightSkewRelMonoid = record
          { identityˡ← = λ q →
            let z≤y∙x , y≤ε = identityʳ← q in y≤ε , comm z≤y∙x
          ; identityʳ→ = λ (z≤y∙x , x≤ε) → identityˡ→ (x≤ε , comm z≤y∙x)
          ; assoc← = λ (z≤y∙xw , xw≤x∙w) →
            let z≤w∙xy , xy≤x∙y = assoc→ (comm xw≤x∙w , comm z≤y∙xw) in
            comm xy≤x∙y , comm z≤w∙xy
          }
        }
      ; comm = comm
      }
    } where open LeftSkewRelMonoid M

  record BicommutativeBimonoid c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      Carrier : Set c
      _≤_ : Rel Carrier ℓ
      η≤_ : Carrier → Set ℓ
      _≤ε : Carrier → Set ℓ
      [_∘_]≤_ : (x y z : Carrier) → Set ℓ
      _≤[_∙_] : (x y z : Carrier) → Set ℓ
      isProset : IsProset _≤_
      η-mono : Monotonic₀₋₁ _≤_ η≤_
      ∘-mono : Monotonic₂₋₁ _≤_ [_∘_]≤_
      ε-mono : Monotonic₁₋₀ _≤_ _≤ε
      ∙-mono : Monotonic₁₋₂ _≤_ _≤[_∙_]
      isBicommutativeBimonoid :
        IsBicommutativeBimonoid _≤_ η≤_ [_∘_]≤_ _≤ε _≤[_∙_]
    open IsProset isProset public
    open IsBicommutativeBimonoid isBicommutativeBimonoid public

    -- TODO: ∘-commutativeRelComonoid, ∙-commutativeRelMonoid

  record RelSemiring c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      Carrier : Set c
      _≤_ : Rel Carrier ℓ
      _≤0 : Carrier → Set ℓ
      _≤[_+_] : (x y z : Carrier) → Set ℓ
      _≤1 : Carrier → Set ℓ
      _≤[_*_] : (x y z : Carrier) → Set ℓ
      isProset : IsProset _≤_
      0-mono : Monotonic₁₋₀ _≤_ _≤0
      +-mono : Monotonic₁₋₂ _≤_ _≤[_+_]
      1-mono : Monotonic₁₋₀ _≤_ _≤1
      *-mono : Monotonic₁₋₂ _≤_ _≤[_*_]
      isRelSemiring : IsRelSemiring _≤_ _≤0 _≤[_+_] _≤1 _≤[_*_]
    open IsProset isProset public
    open IsRelSemiring isRelSemiring public

    +-commutativeRelMonoid : CommutativeRelMonoid c ℓ
    +-commutativeRelMonoid = record
      { isProset = isProset; ε-mono = 0-mono; ∙-mono = +-mono
      ; isCommutativeRelMonoid = +-isCommutativeRelMonoid
      }
    open CommutativeRelMonoid +-commutativeRelMonoid public using () renaming
      ( leftSkewRelMonoid to +-leftSkewRelMonoid
      ; rightSkewRelMonoid to +-rightSkewRelMonoid
      ; relMonoid to +-relMonoid
      ; inter to +-inter; identity²→ to +-identity²→; identity²← to +-identity²←
      )

    *-RelMonoid : RelMonoid c ℓ
    *-RelMonoid = record
      { isProset = isProset; ε-mono = 1-mono; ∙-mono = *-mono
      ; isRelMonoid = *-isRelMonoid
      }
    open RelMonoid *-RelMonoid public using () renaming
      ( leftSkewRelMonoid to *-leftSkewRelMonoid
      ; rightSkewRelMonoid to *-rightSkewRelMonoid
      ; identity²→ to *-identity²→; identity²← to *-identity²←
      )

  record FRelSemiring c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      Carrier : Set c
      _≤_ : Rel Carrier ℓ
      _≤0 : Carrier → Set ℓ
      _≤[_+_] : (x y z : Carrier) → Set ℓ
      _≤1 : Carrier → Set ℓ
      _≤[_*_] : (x y z : Carrier) → Set ℓ
      isProset : IsProset _≤_
      0-mono : Monotonic₁₋₀ _≤_ _≤0
      +-mono : Monotonic₁₋₂ _≤_ _≤[_+_]
      1-mono : Monotonic₁₋₀ _≤_ _≤1
      *-mono : Monotonic₁₋₂ _≤_ _≤[_*_]
      isFRelSemiring : IsFRelSemiring _≤_ _≤0 _≤[_+_] _≤1 _≤[_*_]

    open IsFRelSemiring isFRelSemiring public using
      (isRelSemiring; 0-func; +-func; 1-func; *-func)

    relSemiring : RelSemiring c ℓ
    relSemiring = record
      { isProset = isProset
      ; 0-mono = 0-mono
      ; +-mono = +-mono
      ; 1-mono = 1-mono
      ; *-mono = *-mono
      ; isRelSemiring = isRelSemiring
      }
    open RelSemiring relSemiring public hiding
      ( Carrier; _≤_; _≤0; _≤[_+_]; _≤1; _≤[_*_]; isProset
      ; 0-mono; +-mono; 1-mono; *-mono; isRelSemiring
      )

  -- Modules

  module _ {cr ℓr} (R : RelSemiring cr ℓr) where
    private
      module R = RelSemiring R

    record IsRelLeftSemimodule
      {cm ℓm} {M : Set cm} (_≤ₘ_ : Rel M ℓm)
      (_≤0ₘ : M → Set ℓm) (_≤[_+ₘ_] : M → M → M → Set ℓm)
      (_≤[_*ₘ_] : M → R.Carrier → M → Set ℓm) : Set (cr ⊔ ℓr ⊔ cm ⊔ ℓm)
      where
      field
        +ₘ-isCommutativeRelMonoid : IsCommutativeRelMonoid _≤ₘ_ _≤0ₘ _≤[_+ₘ_]
        *ₘ-identity→ : ∀ {u v} → R._≤1 ◇ v ≤[_*ₘ u ] → v ≤ₘ u
        *ₘ-identity← : ∀ {u v} → v ≤ₘ u → R._≤1 ◇ v ≤[_*ₘ u ]
        *ₘ-assoc→ : ∀ {r s u v} →
          R._≤[ r * s ] ◇ v ≤[_*ₘ u ] → v ≤[ r *ₘ_] ◇ _≤[ s *ₘ u ]
        *ₘ-assoc← : ∀ {r s u v} →
          v ≤[ r *ₘ_] ◇ _≤[ s *ₘ u ] → R._≤[ r * s ] ◇ v ≤[_*ₘ u ]
        *ₘ-annihilˡ→ : ∀ {u v} → R._≤0 ◇ v ≤[_*ₘ u ] → v ≤0ₘ
        *ₘ-annihilˡ← : ∀ {u v} → v ≤0ₘ → R._≤0 ◇ v ≤[_*ₘ u ]
        *ₘ-annihilʳ→ : ∀ {r v} → v ≤[ r *ₘ_] ◇ _≤0ₘ → v ≤0ₘ
        *ₘ-annihilʳ← : ∀ {r v} → v ≤0ₘ → v ≤[ r *ₘ_] ◇ _≤0ₘ
        *ₘ-distribˡ→ : ∀ {r s u v} →
          R._≤[ r + s ] ◇ v ≤[_*ₘ u ] → _≤[ r *ₘ u ] ↘ v ≤[_+ₘ_] ↙ _≤[ s *ₘ u ]
        *ₘ-distribˡ← : ∀ {r s u v} →
          _≤[ r *ₘ u ] ↘ v ≤[_+ₘ_] ↙ _≤[ s *ₘ u ] → R._≤[ r + s ] ◇ v ≤[_*ₘ u ]
        *ₘ-distribʳ→ : ∀ {r u v w} →
          w ≤[ r *ₘ_] ◇ _≤[ u +ₘ v ] → _≤[ r *ₘ u ] ↘ w ≤[_+ₘ_] ↙ _≤[ r *ₘ v ]
        *ₘ-distribʳ← : ∀ {r u v w} →
          _≤[ r *ₘ u ] ↘ w ≤[_+ₘ_] ↙ _≤[ r *ₘ v ] → w ≤[ r *ₘ_] ◇ _≤[ u +ₘ v ]

      open IsCommutativeRelMonoid +ₘ-isCommutativeRelMonoid public
        using () renaming
        ( identityˡ→ to +ₘ-identityˡ→; identityˡ← to +ₘ-identityˡ←
        ; identityʳ→ to +ₘ-identityʳ→; identityʳ← to +ₘ-identityʳ←
        ; assoc→ to +ₘ-assoc→; assoc← to +ₘ-assoc←
        ; comm to +ₘ-comm
        ; isLeftSkewRelMonoid to +ₘ-isLeftSkewRelMonoid
        ; isRightSkewRelMonoid to +ₘ-isRightSkewRelMonoid
        ; isRelMonoid to +ₘ-isRelMonoid
        )

    -- NOTE: I think this structure only really works when *ₘ forms a
    -- Set-monoid (i.e, is total and deterministic).
    record RelLeftSemimodule cm ℓm : Set (cr ⊔ ℓr ⊔ suc (cm ⊔ ℓm)) where
      field
        Carrierₘ : Set cm
        _≤ₘ_ : Rel Carrierₘ ℓm
        _≤0ₘ : Carrierₘ → Set ℓm
        _≤[_+ₘ_] : (x y z : Carrierₘ) → Set ℓm
        _≤[_*ₘ_] : Carrierₘ → R.Carrier → Carrierₘ → Set ℓm
        isProset : IsProset _≤ₘ_
        0ₘ-mono : Monotonic₁₋₀ _≤ₘ_ _≤0ₘ
        +ₘ-mono : Monotonic₁₋₂ _≤ₘ_ _≤[_+ₘ_]
        *ₘ-mono : ∀ {u u′ r r′ v v′} →
          u′ ≤ₘ u → r R.≤ r′ → v ≤ₘ v′ →
          u ≤[ r *ₘ v ] → u′ ≤[ r′ *ₘ v′ ]
        isRelLeftSemimodule : IsRelLeftSemimodule _≤ₘ_ _≤0ₘ _≤[_+ₘ_] _≤[_*ₘ_]
      open IsProset isProset public renaming
        (refl to ≤ₘ-refl; trans to ≤ₘ-trans)
      open IsRelLeftSemimodule isRelLeftSemimodule public

      +ₘ-commutativeRelMonoid : CommutativeRelMonoid cm ℓm
      +ₘ-commutativeRelMonoid = record
        { isProset = isProset; ε-mono = 0ₘ-mono; ∙-mono = +ₘ-mono
        ; isCommutativeRelMonoid = +ₘ-isCommutativeRelMonoid
        }
      open CommutativeRelMonoid +ₘ-commutativeRelMonoid public using () renaming
        ( relMonoid to +ₘ-relMonoid; leftSkewRelMonoid to +ₘ-leftSkewRelMonoid
        ; rightSkewRelMonoid to +ₘ-rightSkewRelMonoid; inter to +ₘ-inter
        ; identity²→ to +ₘ-identity²→; identity²← to +ₘ-identity²←
        )

  module _ {cr ℓr} (R : FRelSemiring cr ℓr) where
    private
      module R = FRelSemiring R

    record IsFRelLeftSemimodule
      {cm ℓm} {M : Set cm} (_≤ₘ_ : Rel M ℓm)
      (_≤0ₘ : M → Set ℓm) (_≤[_+ₘ_] : M → M → M → Set ℓm)
      (_≤[_*ₘ_] : M → R.Carrier → M → Set ℓm) : Set (cr ⊔ ℓr ⊔ cm ⊔ ℓm)
      where
      field
        isRelLeftSemimodule :
          IsRelLeftSemimodule R.relSemiring _≤ₘ_ _≤0ₘ _≤[_+ₘ_] _≤[_*ₘ_]
        0ₘ-func : Universally≤ _≤ₘ_ _≤0ₘ
        +ₘ-func : ∀ u v → Universally≤ _≤ₘ_ _≤[ u +ₘ v ]
        *ₘ-func : ∀ r v → Universally≤ _≤ₘ_ _≤[ r *ₘ v ]

    record FRelLeftSemimodule cm ℓm : Set (cr ⊔ ℓr ⊔ suc (cm ⊔ ℓm)) where
      field
        Carrierₘ : Set cm
        _≤ₘ_ : Rel Carrierₘ ℓm
        _≤0ₘ : Carrierₘ → Set ℓm
        _≤[_+ₘ_] : (x y z : Carrierₘ) → Set ℓm
        _≤[_*ₘ_] : Carrierₘ → R.Carrier → Carrierₘ → Set ℓm
        isProset : IsProset _≤ₘ_
        0ₘ-mono : Monotonic₁₋₀ _≤ₘ_ _≤0ₘ
        +ₘ-mono : Monotonic₁₋₂ _≤ₘ_ _≤[_+ₘ_]
        *ₘ-mono : ∀ {u u′ r r′ v v′} →
          u′ ≤ₘ u → r R.≤ r′ → v ≤ₘ v′ →
          u ≤[ r *ₘ v ] → u′ ≤[ r′ *ₘ v′ ]
        isFRelLeftSemimodule : IsFRelLeftSemimodule _≤ₘ_ _≤0ₘ _≤[_+ₘ_] _≤[_*ₘ_]

      open IsFRelLeftSemimodule isFRelLeftSemimodule public using
        (isRelLeftSemimodule; 0ₘ-func; +ₘ-func; *ₘ-func)

      relLeftSemimodule : RelLeftSemimodule R.relSemiring cm ℓm
      relLeftSemimodule = record
        { isProset = isProset
        ; 0ₘ-mono = 0ₘ-mono
        ; +ₘ-mono = +ₘ-mono
        ; *ₘ-mono = *ₘ-mono
        ; isRelLeftSemimodule = isRelLeftSemimodule
        }
      open RelLeftSemimodule relLeftSemimodule public hiding
        ( Carrierₘ; _≤ₘ_; _≤0ₘ; _≤[_+ₘ_]; _≤[_*ₘ_]; isProset
        ; 0ₘ-mono; +ₘ-mono; *ₘ-mono; isRelLeftSemimodule
        )
