{-# OPTIONS --safe --without-K #-}

module Data.LTree.Matrix.Properties where

  open import Algebra.Core using (Op₂)
  import Algebra.Definitions as Defs
  open import Data.Product
  open import Function.Base using (id; _∘_; flip)
  open import Level using (Level)
  open import Relation.Binary using (Rel)
  open import Relation.Binary.Definitions
  import Relation.Binary.Reasoning.Base.Single as Rea

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Vector.Properties
  open import Data.LTree.Matrix hiding (ident; mult)

  open import Data.Bool

  private
    variable
      a b c d r x y z : Level
      A : Set a
      B : Set b
      C : Set c
      D : Set d
      X : Set x
      Y : Set y
      Z : Set z
      s t u v : LTree

  module Reflᴹ (_∼_ : Rel A r) (refl : Reflexive _∼_) where

    reflᴹ : Reflexive {A = Matrix A s t} (Lift₂ᴹ _∼_)
    reflᴹ .get i j = refl

  module Transᴹ (_∼_ : Rel A r) (trans : Transitive _∼_) where

    transᴹ : Transitive {A = Matrix A s t} (Lift₂ᴹ _∼_)
    transᴹ MM NN .get i j = trans (MM .get i j) (NN .get i j)

  module Mult-cong
    (0# : C) (_+_ : C → C → C) (_*_ : A → B → C)
    (_∼A_ : Rel A x) (_∼B_ : Rel B y) (_∼C_ : Rel C z)
    (open Defs _∼C_)
    (refl : Reflexive _∼C_)
    (+-cong : Congruent₂ _+_)
    (*-cong : ∀ {a a′ b b′} → a ∼A a′ → b ∼B b′ → (a * b) ∼C (a′ * b′))
    where

    open Sum 0# _+_
    open Mult 0# _+_ _*_

    open SumCong _∼C_ 0# _+_ refl +-cong

    *ᴹ-cong : {M M′ : Matrix A s t} {N N′ : Matrix B t u} →
              Lift₂ᴹ _∼A_ M M′ → Lift₂ᴹ _∼B_ N N′ →
              Lift₂ᴹ _∼C_ (M *ᴹ N) (M′ *ᴹ N′)
    *ᴹ-cong MM NN .get i k =
      ∑-cong (mk λ j → *-cong (MM .get i j) (NN .get j k))

  module Plus-cong
    (_+_ : A → B → C)
    (_∼A_ : Rel A x) (_∼B_ : Rel B y) (_∼C_ : Rel C z)
    (+-cong : ∀ {a a′ b b′} → a ∼A a′ → b ∼B b′ → (a + b) ∼C (a′ + b′))
    where

    open Plus _+_

    +ᴹ-cong : {M M′ : Matrix A s t} {N N′ : Matrix B s t} →
              Lift₂ᴹ _∼A_ M M′ → Lift₂ᴹ _∼B_ N N′ →
              Lift₂ᴹ _∼C_ (M +ᴹ N) (M′ +ᴹ N′)
    +ᴹ-cong MM NN .get i j = +-cong (MM .get i j) (NN .get i j)

  module IdentMult
    (0A : A) (1A : A) (_≈_ : Rel B r) (0B : B) (_+_ : Op₂ B) (_*_ : A → B → B)
    (open Defs _≈_)
    (refl : Reflexive _≈_)
    (trans : Transitive _≈_)
    (+-cong : Congruent₂ _+_)
    (+-identity : Identity 0B _+_)
    (1-* : ∀ b → (1A * b) ≈ b)
    (0-* : ∀ b → (0A * b) ≈ 0B)
    where

    open Rea _≈_ refl trans

    open Ident 0A 1A
    open Mult 0B _+_ _*_
    open Sum 0B _+_
    open SumCong _≈_ 0B _+_ refl +-cong
    open Sum0 _≈_ 0B _+_ trans refl +-cong (+-identity .proj₁ 0B)

    private
      infix 4 _≈ᴹ_
      _≈ᴹ_ = Lift₂ᴹ _≈_

    1ᴹ-*ᴹ : (M : Matrix B s t) → 1ᴹ *ᴹ M ≈ᴹ M
    1ᴹ-*ᴹ M .get here k = 1-* _
    1ᴹ-*ᴹ {sl <+> sr} {t} M .get (↙ i) k = begin
      (1ᴹ *ᴹ M) (↙ i) k  ≡⟨⟩
      (1ᴹ *ᴹ (topᴹ M)) i k + (∑ λ j → 0A * botᴹ M j k)
        ∼⟨ +-cong (1ᴹ-*ᴹ (topᴹ M) .get i k)
                  (trans (∑-cong (mk λ j → 0-* (botᴹ M j k))) (∑-0 sr)) ⟩
      topᴹ M i k + 0B          ∼⟨ +-identity .proj₂ _ ⟩
      topᴹ M i k               ≡⟨⟩
      M (↙ i) k          ∎
    1ᴹ-*ᴹ {sl <+> sr} {t} M .get (↘ i) k = begin
      (1ᴹ *ᴹ M) (↘ i) k  ≡⟨⟩
      (∑ λ j → 0A * topᴹ M j k) + (1ᴹ *ᴹ (botᴹ M)) i k
        ∼⟨ +-cong (trans (∑-cong (mk λ j → 0-* (topᴹ M j k))) (∑-0 sl))
                  (1ᴹ-*ᴹ (botᴹ M) .get i k) ⟩
      0B + botᴹ M i k           ∼⟨ +-identity .proj₁ _ ⟩
      botᴹ M i k                ≡⟨⟩
      M (↘ i) k          ∎

  module MultIdent
    (0A : A) (1A : A) (_≈_ : Rel B r) (0B : B) (_+_ : Op₂ B) (_*_ : B → A → B)
    (open Defs _≈_) (let module ⊵ = Defs (flip _≈_))
    (refl : Reflexive _≈_)
    (trans : Transitive _≈_)
    (+-cong : Congruent₂ _+_)
    (+-identity : ⊵.Identity 0B _+_)
    (*-1 : ∀ b → b ≈ (b * 1A))
    (*-0 : ∀ b → 0B ≈ (b * 0A))
    where

    open Rea _≈_ refl trans

    open Ident 0A 1A
    open Mult 0B _+_ _*_
    open Sum 0B _+_
    open SumCong _≈_ 0B _+_ refl +-cong
    open Sum0 (flip _≈_) 0B _+_ (flip trans) refl +-cong (+-identity .proj₂ 0B)

    private
      infix 4 _≈ᴹ_
      _≈ᴹ_ = Lift₂ᴹ _≈_

    *ᴹ-1ᴹ : (M : Matrix B s t) → M ≈ᴹ M *ᴹ 1ᴹ
    *ᴹ-1ᴹ M .get i here = *-1 _
    *ᴹ-1ᴹ {s} {tl <+> tr} M .get i (↙ k) = begin
      M i (↙ k)          ≡⟨⟩
      leftᴹ M i k        ∼⟨ +-identity .proj₂ _ ⟩
      leftᴹ M i k + 0B
        ∼⟨ +-cong (*ᴹ-1ᴹ (leftᴹ M) .get i k)
                  (trans (∑-0 tr) (∑-cong (mk λ j → *-0 (rightᴹ M i j)))) ⟩
      (∑ λ j → leftᴹ M i j * 1ᴹ j k) + (∑ λ j → rightᴹ M i j * 0A)  ≡⟨⟩
      (M *ᴹ 1ᴹ) i (↙ k)  ∎
    *ᴹ-1ᴹ {s} {tl <+> tr} M .get i (↘ k) = begin
      M i (↘ k)          ≡⟨⟩
      rightᴹ M i k       ∼⟨ +-identity .proj₁ _ ⟩
      0B + rightᴹ M i k
        ∼⟨ +-cong (trans (∑-0 tl) (∑-cong (mk λ j → *-0 (leftᴹ M i j))))
                  (*ᴹ-1ᴹ (rightᴹ M) .get i k) ⟩
      (∑ λ j → leftᴹ M i j * 0A) + (∑ λ j → rightᴹ M i j * 1ᴹ j k)  ≡⟨⟩
      (M *ᴹ 1ᴹ) i (↘ k)  ∎

  module MultMult
    (_≈_ : Rel Z r)
    (0# : Z) (_+_ : Op₂ Z)
    (0X : X) (_+X_ : Op₂ X)
    (0Y : Y) (_+Y_ : Op₂ Y)
    (_ˣ*ᶜ_ : X → C → Z) (_ᵃ*ᵇ_ : A → B → X)
    (_ᵃ*ʸ_ : A → Y → Z) (_ᵇ*ᶜ_ : B → C → Y)
    (open Defs _≈_)
    (refl : Reflexive _≈_)
    (trans : Transitive _≈_)
    (+-cong : Congruent₂ _+_)
    (0+0-→ : (0# + 0#) ≈ 0#)
    (0+0-← : 0# ≈ (0# + 0#))
    (exchange : Interchangable _+_ _+_)
    (*-assoc-→ : ∀ x y z → ((x ᵃ*ᵇ y) ˣ*ᶜ z) ≈ (x ᵃ*ʸ (y ᵇ*ᶜ z)))
    (ˣ*ᶜ-zero : ∀ x → (0X ˣ*ᶜ x) ≈ 0#)
    (ˣ*ᶜ-distrib : ∀ x y z → ((y +X z) ˣ*ᶜ x) ≈ ((y ˣ*ᶜ x) + (z ˣ*ᶜ x)))
    (ᵃ*ʸ-zero : ∀ x → 0# ≈ (x ᵃ*ʸ 0Y))
    (ᵃ*ʸ-distrib : ∀ x y z → ((x ᵃ*ʸ y) + (x ᵃ*ʸ z)) ≈ (x ᵃ*ʸ (y +Y z)))
    where

    open Rea _≈_ refl trans

    open Mult 0# _+_  _ˣ*ᶜ_ renaming (_*ᴹ_ to multˣᶜ)
    open Mult 0X _+X_ _ᵃ*ᵇ_ renaming (_*ᴹ_ to multᵃᵇ)
    open Mult 0# _+_  _ᵃ*ʸ_ renaming (_*ᴹ_ to multᵃʸ)
    open Mult 0Y _+Y_ _ᵇ*ᶜ_ renaming (_*ᴹ_ to multᵇᶜ)

    open Sum 0X _+X_ renaming (∑ to ∑X)
    open Sum 0Y _+Y_ renaming (∑ to ∑Y)
    open Sum 0# _+_

    open SumCong _≈_ 0# _+_ refl +-cong renaming (∑-cong to ∑-cong)
    open SumComm _≈_ 0# _+_ refl trans +-cong 0+0-→ 0+0-← exchange

    private
      _≈ᴹ_ = Lift₂ᴹ _≈_

    *ᴹ-*ᴹ-→ : (M : Matrix A s t) (N : Matrix B t u) (O : Matrix C u v) →
              multˣᶜ (multᵃᵇ M N) O ≈ᴹ multᵃʸ M (multᵇᶜ N O)
    *ᴹ-*ᴹ-→ M N O .get i l = begin
      (∑ λ k → (∑X λ j → M i j ᵃ*ᵇ N j k) ˣ*ᶜ O k l)
        ∼⟨ ∑-cong (mk λ k →
             let open SumLinear 0X _+X_ _≈_ 0# _+_ refl trans +-cong
                                (_ˣ*ᶜ O k l) (ˣ*ᶜ-zero _) (ˣ*ᶜ-distrib _) in
             ∑-linear λ j → M i j ᵃ*ᵇ N j k) ⟩
      (∑ λ k → ∑ λ j → (M i j ᵃ*ᵇ N j k) ˣ*ᶜ O k l)
        ∼⟨ ∑-cong (mk λ k → ∑-cong (mk λ j →
             *-assoc-→ (M i j) (N j k) (O k l))) ⟩
      (∑ λ k → ∑ λ j → M i j ᵃ*ʸ (N j k ᵇ*ᶜ O k l))
        ∼⟨ (∑-comm λ k j → M i j ᵃ*ʸ (N j k ᵇ*ᶜ O k l)) ⟩
      (∑ λ j → ∑ λ k → M i j ᵃ*ʸ (N j k ᵇ*ᶜ O k l))
        ∼⟨ ∑-cong (mk λ j →
             let open SumLinear 0Y _+Y_ (flip _≈_) 0# _+_ refl (flip trans)
                                +-cong
                                (M i j ᵃ*ʸ_) (ᵃ*ʸ-zero _) (ᵃ*ʸ-distrib _) in
             ∑-linear λ k → N j k ᵇ*ᶜ O k l) ⟩
      (∑ λ j → M i j ᵃ*ʸ (∑Y λ k → N j k ᵇ*ᶜ O k l))  ∎

  module ZeroMult
    (0A : A) (_≈_ : Rel C r) (0C : C) (_+_ : Op₂ C) (_*_ : A → B → C)
    (open Defs _≈_)
    (refl : Reflexive _≈_)
    (trans : Transitive _≈_)
    (+-cong : Congruent₂ _+_)
    (0+0 : (0C + 0C) ≈ 0C)
    (0-* : ∀ b → (0A * b) ≈ 0C)
    where

    open Rea _≈_ refl trans

    open Zero 0A renaming (0ᴹ to 0ᴹᵃ)
    open Zero 0C renaming (0ᴹ to 0ᴹᶜ)
    open Mult 0C _+_ _*_
    open Sum 0C _+_
    open SumCong _≈_ 0C _+_ refl +-cong
    open Sum0 _≈_ 0C _+_ trans refl +-cong 0+0

    private
      infix 4 _≈ᴹ_
      _≈ᴹ_ = Lift₂ᴹ _≈_

    0ᴹ-*ᴹ : (M : Matrix B t u) → 0ᴹᵃ *ᴹ M ≈ᴹ 0ᴹᶜ {s}
    0ᴹ-*ᴹ {t = t} M .get i k = begin
      (∑ λ j → 0A * M j k)  ∼⟨ ∑-cong (mk λ j → 0-* (M j k)) ⟩
      (∑ {t} λ j → 0C)      ∼⟨ ∑-0 t ⟩
      0C                    ∎

  module MultZero
    (0B : B) (_≈_ : Rel C r) (0C : C) (_+_ : Op₂ C) (_*_ : A → B → C)
    (open Defs _≈_)
    (refl : Reflexive _≈_)
    (trans : Transitive _≈_)
    (+-cong : Congruent₂ _+_)
    (0+0 : 0C ≈ (0C + 0C))
    (*-0 : ∀ a → 0C ≈ (a * 0B))
    where

    open Zero 0B renaming (0ᴹ to 0ᴹᵇ)
    open Zero 0C renaming (0ᴹ to 0ᴹᶜ)
    open Mult 0C _+_ _*_
    open ZeroMult 0B (flip _≈_) 0C _+_ (flip _*_) refl (flip trans)
      +-cong 0+0 *-0

    private
      infix 4 _≈ᴹ_
      _≈ᴹ_ = Lift₂ᴹ _≈_

    *ᴹ-0ᴹ : (M : Matrix A s t) → 0ᴹᶜ {s} {u} ≈ᴹ M *ᴹ 0ᴹᵇ
    *ᴹ-0ᴹ M .get i k = 0ᴹ-*ᴹ (M ᵀ) .get k i

  module PlusMult
    (_+A_ : Op₂ A) (_≈_ : Rel C r) (0C : C) (_+C_ : Op₂ C) (_*_ : A → B → C)
    (open Defs _≈_)
    (refl : Reflexive _≈_)
    (trans : Transitive _≈_)
    (+C-cong : Congruent₂ _+C_)
    (0+0 : 0C ≈ (0C +C 0C))
    (+++ : Interchangable _+C_ _+C_)
    (+-* : ∀ x y b → ((x +A y) * b) ≈ ((x * b) +C (y * b)))
    where

    open Rea _≈_ refl trans

    open Plus _+A_ renaming (_+ᴹ_ to _+ᴹᵃ_)
    open Plus _+C_ renaming (_+ᴹ_ to _+ᴹᶜ_)
    open Mult 0C _+C_ _*_
    open Sum 0C _+C_
    open SumCong _≈_ 0C _+C_ refl +C-cong
    open Sum+ _≈_ 0C _+C_ refl trans +C-cong 0+0 +++

    private
      infix 4 _≈ᴹ_
      _≈ᴹ_ = Lift₂ᴹ _≈_

    +ᴹ-*ᴹ : (M N : Matrix A s t) (O : Matrix B t u) →
            (M +ᴹᵃ N) *ᴹ O ≈ᴹ M *ᴹ O +ᴹᶜ N *ᴹ O
    +ᴹ-*ᴹ {t = t} M N O .get i k = begin
      (∑ λ j → (M i j +A N i j) * O j k)
                                      ∼⟨ ∑-cong {t} (mk λ j → +-* _ _ _) ⟩
      (∑ λ j → (M i j * O j k) +C (N i j * O j k))        ∼⟨ ∑-+ {t} _ _ ⟩
      (∑ λ j → M i j * O j k) +C (∑ λ j → N i j * O j k)  ∎

  module LeftScaleMult
    (_≈_ : Rel Z r) (0Y : Y) (_+Y_ : Op₂ Y) (0Z : Z) (_+Z_ : Op₂ Z)
    (_*ᵃᵇ_ : A → B → X) (_*ᵇᶜ_ : B → C → Y)
    (_*ˣᶜ_ : X → C → Z) (_*ᵃʸ_ : A → Y → Z)
    (open Defs _≈_)
    (refl : Reflexive _≈_)
    (trans : Transitive _≈_)
    (+Z-cong : Congruent₂ _+Z_)
    (*-0 : ∀ x → 0Z ≈ (x *ᵃʸ 0Y))
    (*-+ : ∀ x y z → ((x *ᵃʸ y) +Z (x *ᵃʸ z)) ≈ (x *ᵃʸ (y +Y z)))
    (*-* : ∀ x y z → ((x *ᵃᵇ y) *ˣᶜ z) ≈ (x *ᵃʸ (y *ᵇᶜ z)))
    where

    open Rea _≈_ refl trans

    open LeftScale _*ᵃᵇ_ renaming (_*ₗ_ to _*ₗᵃᵇ_)
    open LeftScale _*ᵃʸ_ renaming (_*ₗ_ to _*ₗᵃʸ_)
    open Mult 0Y _+Y_ _*ᵇᶜ_ renaming (_*ᴹ_ to _*ᴹᵇᶜ_)
    open Mult 0Z _+Z_ _*ˣᶜ_ renaming (_*ᴹ_ to _*ᴹˣᶜ_)
    open Sum 0Y _+Y_ renaming (∑ to ∑Y)
    open Sum 0Z _+Z_ renaming (∑ to ∑Z)
    open SumCong _≈_ 0Z _+Z_ refl +Z-cong

    private
      infix 4 _≈ᴹ_
      _≈ᴹ_ = Lift₂ᴹ _≈_

    *ₗ-*ᴹ : ∀ x (M : Matrix B s t) (N : Matrix C t u) →
            (x *ₗᵃᵇ M) *ᴹˣᶜ N ≈ᴹ x *ₗᵃʸ (M *ᴹᵇᶜ N)
    *ₗ-*ᴹ {t = t} x M N .get i k = begin
      (∑Z λ j → (x *ᵃᵇ M i j) *ˣᶜ N j k)  ∼⟨ ∑-cong {t} (mk λ j → *-* _ _ _) ⟩
      (∑Z λ j → x *ᵃʸ (M i j *ᵇᶜ N j k))  ∼⟨ ∑-linear {t} _ ⟩
      x *ᵃʸ (∑Y λ j → M i j *ᵇᶜ N j k)    ∎
      where
      open SumLinear 0Y _+Y_ (flip _≈_) 0Z _+Z_ refl (flip trans) +Z-cong
                     (x *ᵃʸ_) (*-0 x) (*-+ x)
