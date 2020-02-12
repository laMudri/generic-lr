{-# OPTIONS --safe --without-K #-}

module Data.LTree.Matrix.Properties where

  open import Algebra.Core using (Op₂)
  import Algebra.Definitions as Defs
  open import Data.Product
  open import Function.Base using (id; _∘_; _∘′_; _∋_; flip)
  open import Level using (Level)
  open import Relation.Binary using (Rel)
  open import Relation.Binary.Definitions
  import Relation.Binary.Reasoning.Base.Single as Rea

  open import Data.LTree
  open import Data.LTree.Vector
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

  module Sum (0# : A) (_+_ : Op₂ A) where
    ∑ = fold id 0# _+_

  module SumCong
    (_≈_ : Rel A r) (0# : A) (_+_ : Op₂ A) (open Defs _≈_)
    (0-cong : 0# ≈ 0#)
    (+-cong : Congruent₂ _+_)
    where

    open Sum 0# _+_

    ∑-cong : ∀ {s} {u v : Vector A s} → Lift₂ _≈_ u v → ∑ u ≈ ∑ v
    ∑-cong {[-]} (mk qs) = qs here
    ∑-cong {ε} (mk qs) = 0-cong
    ∑-cong {s <+> t} (mk qs) =
      +-cong (∑-cong (mk (qs ∘ go-left))) (∑-cong (mk (qs ∘ go-right)))

  module Sum0
    (_≈_ : Rel A r) (0# : A) (_+_ : Op₂ A)
    (open Defs _≈_)
    (trans : Transitive _≈_)
    (0-cong : 0# ≈ 0#)
    (+-cong : Congruent₂ _+_)
    (0+0 : (0# + 0#) ≈ 0#)
    where

    open Sum 0# _+_

    ∑-0 : ∀ s → ∑ {s} (λ _ → 0#) ≈ 0#
    ∑-0 [-] = 0-cong
    ∑-0 ε = 0-cong
    ∑-0 (s <+> t) = trans (+-cong (∑-0 s) (∑-0 t)) 0+0

  module Sum+
    (_≈_ : Rel A r) (0# : A) (_+_ : Op₂ A)
    (open Defs _≈_)
    (refl : Reflexive _≈_)
    (trans : Transitive _≈_)
    (+-cong : Congruent₂ _+_)
    (0+0 : 0# ≈ (0# + 0#))
    (exchange : Interchangable _+_ _+_)
    where

    open Sum 0# _+_

    ∑-+ : (u v : Vector A s) → ∑ (λ i → u i + v i) ≈ (∑ u + ∑ v)
    ∑-+ {[-]} u v = refl
    ∑-+ {ε} u v = 0+0
    ∑-+ {s <+> t} u v =
      trans (+-cong (∑-+ (u ∘ go-left) (v ∘ go-left))
                    (∑-+ (u ∘ go-right) (v ∘ go-right)))
            (exchange _ _ _ _)

  module SumLinear
    (0A : A) (_+A_ : Op₂ A)
    (_≈_ : Rel B r) (0B : B) (_+B_ : Op₂ B)
    (open Defs _≈_)
    (refl : Reflexive _≈_)
    (trans : Transitive _≈_)
    (+-cong : Congruent₂ _+B_)
    (f : A → B)
    (f-0 : f 0A ≈ 0B)
    (f-+ : ∀ x y → f (x +A y) ≈ (f x +B f y))
    where

    open Sum 0A _+A_ renaming (∑ to ∑A)
    open Sum 0B _+B_ renaming (∑ to ∑B)

    ∑-linear : ∀ {s} (u : Vector A s) → f (∑A u) ≈ ∑B (f ∘ u)
    ∑-linear {[-]} u = refl
    ∑-linear {ε} u = f-0
    ∑-linear {s <+> t} u =
      trans (f-+ (∑A (u ∘ go-left)) (∑A (u ∘ go-right)))
            (+-cong (∑-linear (u ∘ go-left)) (∑-linear (u ∘ go-right)))

  module SumComm
    (_≈_ : Rel A r) (0# : A) (_+_ : Op₂ A)
    (open Defs _≈_)
    (refl : Reflexive _≈_)
    (trans : Transitive _≈_)
    (+-cong : Congruent₂ _+_)
    (0+0-→ : (0# + 0#) ≈ 0#)
    (0+0-← : 0# ≈ (0# + 0#))
    (exchange : Interchangable _+_ _+_)
    where

    open Sum 0# _+_
    open Sum0 _≈_ 0# _+_ trans refl +-cong 0+0-→
    open Sum+ _≈_ 0# _+_ refl trans +-cong 0+0-← exchange

    ∑-comm : (M : Matrix A s t) →
             (∑ λ i → ∑ λ j → M i j) ≈ (∑ λ j → ∑ λ i → M i j)
    ∑-comm {s} {[-]} M = refl
    ∑-comm {s} {ε} M = ∑-0 s
    ∑-comm {s} {tl <+> tr} M =
      trans (∑-+ (λ i → ∑ (leftᴹ M i)) (λ i → ∑ (rightᴹ M i)))
            (+-cong (∑-comm (leftᴹ M)) (∑-comm (rightᴹ M)))

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

    infix 4 _≈ᴹ_
    _≈ᴹ_ = Lift₂ᴹ _≈_

    1ᴹ-*ᴹ : (M : Matrix B s t) → 1ᴹ *ᴹ M ≈ᴹ M
    1ᴹ-*ᴹ M .get here k = 1-* _
    1ᴹ-*ᴹ {sl <+> sr} {t} M .get (go-left i) k = begin
      (1ᴹ *ᴹ M) (go-left i) k  ≡⟨⟩
      (1ᴹ *ᴹ (topᴹ M)) i k + (∑ λ j → 0A * botᴹ M j k)
        ∼⟨ +-cong (1ᴹ-*ᴹ (topᴹ M) .get i k)
                  (trans (∑-cong (mk λ j → 0-* (botᴹ M j k))) (∑-0 sr)) ⟩
      topᴹ M i k + 0B          ∼⟨ +-identity .proj₂ _ ⟩
      topᴹ M i k               ≡⟨⟩
      M (go-left i) k          ∎
    1ᴹ-*ᴹ {sl <+> sr} {t} M .get (go-right i) k = begin
      (1ᴹ *ᴹ M) (go-right i) k  ≡⟨⟩
      (∑ λ j → 0A * topᴹ M j k) + (1ᴹ *ᴹ (botᴹ M)) i k
        ∼⟨ +-cong (trans (∑-cong (mk λ j → 0-* (topᴹ M j k))) (∑-0 sl))
                  (1ᴹ-*ᴹ (botᴹ M) .get i k) ⟩
      0B + botᴹ M i k           ∼⟨ +-identity .proj₁ _ ⟩
      botᴹ M i k                ≡⟨⟩
      M (go-right i) k          ∎

  module MultIdent
    (0A : A) (1A : A) (_≈_ : Rel B r) (0B : B) (_+_ : Op₂ B) (_*_ : B → A → B)
    (open Defs _≈_)
    (refl : Reflexive _≈_)
    (trans : Transitive _≈_)
    (+-cong : Congruent₂ _+_)
    (+-identity : Identity 0B _+_)
    (*-1 : ∀ b → (b * 1A) ≈ b)
    (*-0 : ∀ b → (b * 0A) ≈ 0B)
    where

    open Rea _≈_ refl trans

    open Ident 0A 1A
    open Mult 0B _+_ _*_
    open Sum 0B _+_
    open SumCong _≈_ 0B _+_ refl +-cong
    open Sum0 _≈_ 0B _+_ trans refl +-cong (+-identity .proj₁ 0B)

    infix 4 _≈ᴹ_
    _≈ᴹ_ = Lift₂ᴹ _≈_

    *ᴹ-1ᴹ : (M : Matrix B s t) → M *ᴹ 1ᴹ ≈ᴹ M
    *ᴹ-1ᴹ M .get i here = *-1 _
    *ᴹ-1ᴹ {s} {tl <+> tr} M .get i (go-left k) = begin
      (M *ᴹ 1ᴹ) i (go-left k)  ≡⟨⟩
      (∑ λ j → leftᴹ M i j * 1ᴹ j k) + (∑ λ j → rightᴹ M i j * 0A)
        ∼⟨ +-cong (*ᴹ-1ᴹ (leftᴹ M) .get i k)
                  (trans (∑-cong (mk λ j → *-0 (rightᴹ M i j))) (∑-0 tr)) ⟩
      leftᴹ M i k + 0B         ∼⟨ +-identity .proj₂ _ ⟩
      leftᴹ M i k              ≡⟨⟩
      M i (go-left k)          ∎
    *ᴹ-1ᴹ {s} {tl <+> tr} M .get i (go-right k) = begin
      (M *ᴹ 1ᴹ) i (go-right k)  ≡⟨⟩
      (∑ λ j → leftᴹ M i j * 0A) + (∑ λ j → rightᴹ M i j * 1ᴹ j k)
        ∼⟨ +-cong (trans (∑-cong (mk λ j → *-0 (leftᴹ M i j))) (∑-0 tl))
                  (*ᴹ-1ᴹ (rightᴹ M) .get i k) ⟩
      0B + rightᴹ M i k         ∼⟨ +-identity .proj₁ _ ⟩
      rightᴹ M i k              ≡⟨⟩
      M i (go-right k)          ∎

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
