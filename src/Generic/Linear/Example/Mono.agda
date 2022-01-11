{-# OPTIONS --safe --without-K --postfix-projections #-}

module Generic.Linear.Example.Mono where

  open import Algebra using (Op₂; IsCommutativeMonoid; Congruent₂)
  open import Algebra.Po
  open import Algebra.Relational
  open import Data.Product
  open import Data.Unit using (⊤; tt)
  open import Level
  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary using (U; _∩_)
  open import Relation.Unary.Bunched
  open BunchedDuplicable

  infix 7 _*_
  infix 5 _∧_
  infix 4 _≤_

  data WayUp : Set where
    ↑↑ ↓↓ ?? ~~ : WayUp

  data _≤_ : (a b : WayUp) → Set where
    ≤-refl : ∀ {a} → a ≤ a
    ≡≤↑ : ~~ ≤ ↑↑
    ≡≤↓ : ~~ ≤ ↓↓
    ↑≤? : ↑↑ ≤ ??
    ↓≤? : ↓↓ ≤ ??
    ≡≤? : ~~ ≤ ??

  _∧_ : Op₂ WayUp
  ↑↑ ∧ ↑↑ = ↑↑
  ↑↑ ∧ ↓↓ = ~~
  ↑↑ ∧ ?? = ↑↑
  ↑↑ ∧ ~~ = ~~
  ↓↓ ∧ ↑↑ = ~~
  ↓↓ ∧ ↓↓ = ↓↓
  ↓↓ ∧ ?? = ↓↓
  ↓↓ ∧ ~~ = ~~
  ?? ∧ b = b
  ~~ ∧ b = ~~

  _*_ : Op₂ WayUp
  ↑↑ * b = b
  ↓↓ * ↑↑ = ↓↓
  ↓↓ * ↓↓ = ↑↑
  ↓↓ * ?? = ??
  ↓↓ * ~~ = ~~
  ?? * b = ??
  ~~ * ↑↑ = ~~
  ~~ * ↓↓ = ~~
  ~~ * ?? = ??
  ~~ * ~~ = ~~

  rawPoSemiring : RawPoSemiring 0ℓ 0ℓ 0ℓ
  rawPoSemiring = record
    { rawPoset = record { Carrier = WayUp ; _≈_ = _≡_ ; _≤_ = _≤_ }
    ; 0# = ??
    ; _+_ = _∧_
    ; 1# = ↑↑
    ; _*_ = _*_
    }

  ~~≤ : ∀ {b} → ~~ ≤ b
  ~~≤ {↑↑} = ≡≤↑
  ~~≤ {↓↓} = ≡≤↓
  ~~≤ {??} = ≡≤?
  ~~≤ {~~} = ≤-refl

  ≤?? : ∀ {a} → a ≤ ??
  ≤?? {↑↑} = ↑≤?
  ≤?? {↓↓} = ↓≤?
  ≤?? {??} = ≤-refl
  ≤?? {~~} = ≡≤?

  ≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
  ≤-trans ≤-refl bc = bc
  ≤-trans ≡≤↑ bc = ~~≤
  ≤-trans ≡≤↓ bc = ~~≤
  ≤-trans ↑≤? ≤-refl = ↑≤?
  ≤-trans ↓≤? ≤-refl = ↓≤?
  ≤-trans ≡≤? ≤-refl = ≡≤?

  ≤-antisym : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b
  ≤-antisym ≤-refl ba = refl

  Top : Set
  Top = Universally≤ _≤_ U

  top : Top
  top .witness = ??
  top .holds = _
  top .unique _ = ≤??

  Meet : (a b : WayUp) → Set
  Meet a b = Universally≤ _≤_ ((_≤ a) ∩ (_≤ b))

  meet : ∀ a b → Meet a b
  meet a b .witness = a ∧ b
  meet ↑↑ ↑↑ .holds = ≤-refl , ≤-refl
  meet ↑↑ ↓↓ .holds = ≡≤↑ , ≡≤↓
  meet ↑↑ ?? .holds = ≤-refl , ↑≤?
  meet ↑↑ ~~ .holds = ≡≤↑ , ≤-refl
  meet ↓↓ ↑↑ .holds = ≡≤↓ , ≡≤↑
  meet ↓↓ ↓↓ .holds = ≤-refl , ≤-refl
  meet ↓↓ ?? .holds = ≤-refl , ↓≤?
  meet ↓↓ ~~ .holds = ≡≤↓ , ≤-refl
  meet ?? b .holds = ≤?? , ≤-refl
  meet ~~ b .holds = ~~≤ , ~~≤
  meet ↑↑ .↑↑ .unique (≤-refl , ≤-refl) = ≤-refl
  meet ↑↑ .?? .unique (≤-refl , ↑≤?) = ≤-refl
  meet ↓↓ .↓↓ .unique (≤-refl , ≤-refl) = ≤-refl
  meet ↓↓ .?? .unique (≤-refl , ↓≤?) = ≤-refl
  meet ?? b .unique (≤-refl , ≤b) = ≤b
  meet ~~ b .unique (≤-refl , ≤b) = ≤-refl
  meet .↑↑ b .unique (≡≤↑ , ≤b) = ~~≤
  meet .↓↓ b .unique (≡≤↓ , ≤b) = ~~≤
  meet .?? b .unique (↑≤? , ≤b) = ≤b
  meet .?? b .unique (↓≤? , ≤b) = ≤b
  meet .?? b .unique (≡≤? , ≤b) = ≤b

  module WithMeet (m : ∀ a b → Meet a b) where

    private
      infix 5 _∧′_
      _∧′_ : Op₂ WayUp
      a ∧′ b = m a b .witness

      module M {a b} = Universally≤ (m a b)
    open M using () renaming (holds to mh; unique to mu)
    private
      mh1 : ∀ {a b} → a ∧′ b ≤ a
      mh1 = mh .proj₁
      mh2 : ∀ {a b} → a ∧′ b ≤ b
      mh2 = mh .proj₂

    meet-mono : ∀ {a a′ b b′} → a ≤ a′ → b ≤ b′ →
      a ∧′ b ≤ a′ ∧′ b′
    meet-mono aa bb = mu (≤-trans mh1 aa , ≤-trans mh2 bb)

    meet-comm : ∀ a b → a ∧′ b ≡ b ∧′ a
    meet-comm a b = ≤-antisym
      (mu (mh2 , mh1))
      (mu (mh2 , mh1))

    meet-assoc : ∀ a b c → (a ∧′ b) ∧′ c ≡ a ∧′ (b ∧′ c)
    meet-assoc a b c = ≤-antisym
      (mu (≤-trans mh1 mh1 , mu (≤-trans mh1 mh2 , mh2)))
      (mu (mu (mh1 , ≤-trans mh2 mh1) , ≤-trans mh2 mh2))

    module WithTop (t : Top) where
      open Universally≤ t using () renaming (witness to ⊤′; unique to tu)

      meet-identityˡ : ∀ a → ⊤′ ∧′ a ≡ a
      meet-identityˡ a = ≤-antisym mh2 (mu (tu _ , ≤-refl))

      meet-identityʳ : ∀ a → a ∧′ ⊤′ ≡ a
      meet-identityʳ a = ≤-antisym mh1 (mu (≤-refl , tu _))

      meet-isCommutativeMonoid : IsCommutativeMonoid _≡_ _∧′_ ⊤′
      meet-isCommutativeMonoid = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = isEquivalence
              ; ∙-cong = cong₂ _∧′_
              }
            ; assoc = meet-assoc
            }
          ; identity = meet-identityˡ , meet-identityʳ
          }
        ; comm = meet-comm
        }

  open WithMeet meet
  open WithTop top

  *-mono : Congruent₂ _≤_ _*_
  *-mono {↑↑} {.↑↑} {b} {b′} ≤-refl bb = bb
  *-mono {↑↑} {.??} {b} {b′} ↑≤? bb = ≤??
  *-mono {↓↓} {.↓↓} {↑↑} {.↑↑} ≤-refl ≤-refl = ≤-refl
  *-mono {↓↓} {.↓↓} {↑↑} {.??} ≤-refl ↑≤? = ↓≤?
  *-mono {↓↓} {.↓↓} {↓↓} {.↓↓} ≤-refl ≤-refl = ≤-refl
  *-mono {↓↓} {.↓↓} {↓↓} {.??} ≤-refl ↓≤? = ↑≤?
  *-mono {↓↓} {.↓↓} {??} {.??} ≤-refl ≤-refl = ≤-refl
  *-mono {↓↓} {.↓↓} {~~} {b′} ≤-refl bb = ~~≤
  *-mono {↓↓} {.??} {b} {b′} ↓≤? bb = ≤??
  *-mono {??} {.??} {b} {b′} ≤-refl bb = ≤-refl
  *-mono {~~} {a′} {↑↑} {b′} aa bb = ~~≤
  *-mono {~~} {a′} {↓↓} {b′} aa bb = ~~≤
  *-mono {~~} {.~~} {??} {.??} ≤-refl ≤-refl = ≤-refl
  *-mono {~~} {.↑↑} {??} {.??} ≡≤↑ ≤-refl = ≤-refl
  *-mono {~~} {.↓↓} {??} {.??} ≡≤↓ ≤-refl = ≤-refl
  *-mono {~~} {.??} {??} {.??} ≡≤? ≤-refl = ≤-refl
  *-mono {~~} {a′} {~~} {b′} aa bb = ~~≤

  *-identityˡ : ∀ a → ↑↑ * a ≡ a
  *-identityˡ a = refl
  *-identityʳ : ∀ a → a * ↑↑ ≡ a
  *-identityʳ ↑↑ = refl
  *-identityʳ ↓↓ = refl
  *-identityʳ ?? = refl
  *-identityʳ ~~ = refl
  *-assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)
  *-assoc ↑↑ b c = refl
  *-assoc ↓↓ ↑↑ c = refl
  *-assoc ↓↓ ↓↓ ↑↑ = refl
  *-assoc ↓↓ ↓↓ ↓↓ = refl
  *-assoc ↓↓ ↓↓ ?? = refl
  *-assoc ↓↓ ↓↓ ~~ = refl
  *-assoc ↓↓ ?? c = refl
  *-assoc ↓↓ ~~ ↑↑ = refl
  *-assoc ↓↓ ~~ ↓↓ = refl
  *-assoc ↓↓ ~~ ?? = refl
  *-assoc ↓↓ ~~ ~~ = refl
  *-assoc ?? b c = refl
  *-assoc ~~ ↑↑ c = refl
  *-assoc ~~ ↓↓ ↑↑ = refl
  *-assoc ~~ ↓↓ ↓↓ = refl
  *-assoc ~~ ↓↓ ?? = refl
  *-assoc ~~ ↓↓ ~~ = refl
  *-assoc ~~ ?? c = refl
  *-assoc ~~ ~~ ↑↑ = refl
  *-assoc ~~ ~~ ↓↓ = refl
  *-assoc ~~ ~~ ?? = refl
  *-assoc ~~ ~~ ~~ = refl

  *-zeroˡ : ∀ a → ?? * a ≡ ??
  *-zeroˡ a = refl
  *-zeroʳ : ∀ a → a * ?? ≡ ??
  *-zeroʳ ↑↑ = refl
  *-zeroʳ ↓↓ = refl
  *-zeroʳ ?? = refl
  *-zeroʳ ~~ = refl

  *-distribˡ : ∀ a b c → (b ∧ c) * a ≡ (b * a) ∧ (c * a)
  *-distribˡ ↑↑ ↑↑ ↑↑ = refl
  *-distribˡ ↑↑ ↑↑ ↓↓ = refl
  *-distribˡ ↑↑ ↑↑ ?? = refl
  *-distribˡ ↑↑ ↑↑ ~~ = refl
  *-distribˡ ↓↓ ↑↑ ↑↑ = refl
  *-distribˡ ↓↓ ↑↑ ↓↓ = refl
  *-distribˡ ↓↓ ↑↑ ?? = refl
  *-distribˡ ↓↓ ↑↑ ~~ = refl
  *-distribˡ ?? ↑↑ ↑↑ = refl
  *-distribˡ ?? ↑↑ ↓↓ = refl
  *-distribˡ ?? ↑↑ ?? = refl
  *-distribˡ ?? ↑↑ ~~ = refl
  *-distribˡ ~~ ↑↑ ↑↑ = refl
  *-distribˡ ~~ ↑↑ ↓↓ = refl
  *-distribˡ ~~ ↑↑ ?? = refl
  *-distribˡ ~~ ↑↑ ~~ = refl
  *-distribˡ ↑↑ ↓↓ ↑↑ = refl
  *-distribˡ ↑↑ ↓↓ ↓↓ = refl
  *-distribˡ ↑↑ ↓↓ ?? = refl
  *-distribˡ ↑↑ ↓↓ ~~ = refl
  *-distribˡ ↓↓ ↓↓ ↑↑ = refl
  *-distribˡ ↓↓ ↓↓ ↓↓ = refl
  *-distribˡ ↓↓ ↓↓ ?? = refl
  *-distribˡ ↓↓ ↓↓ ~~ = refl
  *-distribˡ ?? ↓↓ ↑↑ = refl
  *-distribˡ ?? ↓↓ ↓↓ = refl
  *-distribˡ ?? ↓↓ ?? = refl
  *-distribˡ ?? ↓↓ ~~ = refl
  *-distribˡ ~~ ↓↓ ↑↑ = refl
  *-distribˡ ~~ ↓↓ ↓↓ = refl
  *-distribˡ ~~ ↓↓ ?? = refl
  *-distribˡ ~~ ↓↓ ~~ = refl
  *-distribˡ a ?? c = refl
  *-distribˡ ↑↑ ~~ c = refl
  *-distribˡ ↓↓ ~~ c = refl
  *-distribˡ ?? ~~ ↑↑ = refl
  *-distribˡ ?? ~~ ↓↓ = refl
  *-distribˡ ?? ~~ ?? = refl
  *-distribˡ ?? ~~ ~~ = refl
  *-distribˡ ~~ ~~ c = refl
  *-distribʳ : ∀ a b c → a * (b ∧ c) ≡ (a * b) ∧ (a * c)
  *-distribʳ ↑↑ b c = refl
  *-distribʳ ↓↓ ↑↑ ↑↑ = refl
  *-distribʳ ↓↓ ↑↑ ↓↓ = refl
  *-distribʳ ↓↓ ↑↑ ?? = refl
  *-distribʳ ↓↓ ↑↑ ~~ = refl
  *-distribʳ ↓↓ ↓↓ ↑↑ = refl
  *-distribʳ ↓↓ ↓↓ ↓↓ = refl
  *-distribʳ ↓↓ ↓↓ ?? = refl
  *-distribʳ ↓↓ ↓↓ ~~ = refl
  *-distribʳ ↓↓ ?? c = refl
  *-distribʳ ↓↓ ~~ c = refl
  *-distribʳ ?? b c = refl
  *-distribʳ ~~ ↑↑ ↑↑ = refl
  *-distribʳ ~~ ↑↑ ↓↓ = refl
  *-distribʳ ~~ ↑↑ ?? = refl
  *-distribʳ ~~ ↑↑ ~~ = refl
  *-distribʳ ~~ ↓↓ ↑↑ = refl
  *-distribʳ ~~ ↓↓ ↓↓ = refl
  *-distribʳ ~~ ↓↓ ?? = refl
  *-distribʳ ~~ ↓↓ ~~ = refl
  *-distribʳ ~~ ?? c = refl
  *-distribʳ ~~ ~~ c = refl

  poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ
  poSemiring = record
    { RawPoSemiring rawPoSemiring
    ; isPoSemiring = record
      { isPartialOrder = record
        { isPreorder = record
          { isEquivalence = isEquivalence
          ; reflexive = λ { refl → ≤-refl }
          ; trans = ≤-trans
          }
        ; antisym = ≤-antisym
        }
      ; isSemiring = record
        { isSemiringWithoutAnnihilatingZero = record
          { +-isCommutativeMonoid = meet-isCommutativeMonoid
          ; *-isMonoid = record
            { isSemigroup = record
              { isMagma = record
                { isEquivalence = isEquivalence
                ; ∙-cong = cong₂ _*_
                }
              ; assoc = *-assoc
              }
            ; identity = *-identityˡ , *-identityʳ
            }
          ; distrib = *-distribʳ , *-distribˡ
          }
        ; zero = *-zeroˡ , *-zeroʳ
        }
      ; +-mono = meet-mono
      ; *-mono = *-mono
      }
    }

  ↓↓-involutive : ∀ a → ↓↓ * (↓↓ * a) ≡ a
  ↓↓-involutive ↑↑ = refl
  ↓↓-involutive ↓↓ = refl
  ↓↓-involutive ?? = refl
  ↓↓-involutive ~~ = refl

  open import Data.List

  ??⁻¹ : ∀ a → List (a ≤ ??)
  ??⁻¹ a = ≤?? ∷ []

  ∧⁻¹ : ∀ a → List (Σ (_ × _) \ (b , c) → a ≤ b ∧ c)
  ∧⁻¹ a = ((a , a) , meet a a .unique (≤-refl , ≤-refl)) ∷ []

  ↑↑⁻¹ : ∀ a → List (a ≤ ↑↑)
  ↑↑⁻¹ ↑↑ = ≤-refl ∷ []
  ↑↑⁻¹ ↓↓ = []
  ↑↑⁻¹ ?? = []
  ↑↑⁻¹ ~~ = ≡≤↑ ∷ []

  *⁻¹ : ∀ b a → List (∃ \ c → a ≤ b * c)
  *⁻¹ ↑↑ a = (a , ≤-refl) ∷ []
  *⁻¹ ↓↓ a = (↓↓ * a , subst (a ≤_) (sym (↓↓-involutive a)) ≤-refl) ∷ []
  *⁻¹ ?? a = (~~ , ≤??) ∷ []
  *⁻¹ ~~ ↑↑ = (?? , ↑≤?) ∷ []
  *⁻¹ ~~ ↓↓ = (?? , ↓≤?) ∷ []
  *⁻¹ ~~ ?? = (?? , ≤-refl) ∷ []
  *⁻¹ ~~ ~~ = (~~ , ~~≤) ∷ []

  rep : ∀ a → List (Dup _≤_ (_≤ ??) (λ x y z → x ≤ y ∧ z) (λ _ → ⊤) a)
  rep a = □⟨ ≤-refl , ≤?? , meet a a .unique (≤-refl , ≤-refl) ⟩ _ ∷ []
