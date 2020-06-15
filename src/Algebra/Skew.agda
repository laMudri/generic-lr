{-# OPTIONS --without-K --safe --postfix-projections #-}

module Algebra.Skew where

  open import Algebra.Core
  import Algebra.Skew.Definitions as Defs
  import Algebra.Skew.Definitions.Left as LeftDefs
  import Algebra.Skew.Definitions.Right as RightDefs
  import Algebra.Skew.Definitions.Both as BothDefs
  open import Function.Base using (flip)
  open import Level
  open import Relation.Binary.Core using (Rel; _Preserves_⟶_)
  open import Relation.Binary.Definitions

  record IsProset {c ℓ} {C : Set c} (≤ : Rel C ℓ) : Set (c ⊔ ℓ) where
    field
      refl : Reflexive ≤
      trans : Transitive ≤

  record Proset c ℓ : Set (suc (c ⊔ ℓ)) where
    infix 4 _≤_
    field
      Carrier : Set c
      _≤_ : Rel Carrier ℓ
      isProset : IsProset _≤_
    open IsProset isProset public

  record ProsetMor {p pℓ q qℓ} (P : Proset p pℓ) (Q : Proset q qℓ)
                   : Set (p ⊔ pℓ ⊔ q ⊔ qℓ) where
    private
      module P = Proset P
      module Q = Proset Q
    field
      apply : P.Carrier → Q.Carrier
      hom-mono : ∀ {x y} → x P.≤ y → apply x Q.≤ apply y

  module _ where
    open Proset
    open IsProset

    _ᵒᵖ : ∀ {c ℓ} → Proset c ℓ → Proset c ℓ
    (P ᵒᵖ) .Carrier = P .Carrier
    (P ᵒᵖ) ._≤_ = flip (P ._≤_)
    (P ᵒᵖ) .isProset .refl = P .isProset .refl
    (P ᵒᵖ) .isProset .trans = flip (P .isProset .trans)

  --

  record MonoOp₂ {c ℓ} {C : Set c} (≤ : Rel C ℓ) : Set (c ⊔ ℓ) where
    infix 5 _∙_
    open Defs ≤
    field
      _∙_ : Op₂ C
      mono : Monotonic₂ _∙_

  module _ where
    open MonoOp₂

    _ᵒᵖ₂ : ∀ {c ℓ} {C : Set c} {≤ : Rel C ℓ} → MonoOp₂ ≤ → MonoOp₂ (flip ≤)
    (o ᵒᵖ₂) ._∙_ = o ._∙_
    (o ᵒᵖ₂) .mono = o .mono

  record MonoOpₗ {a m ℓ ℓ′} {A : Set a} {M : Set m}
                 (≤ : Rel A ℓ′) (≤ₘ : Rel M ℓ) : Set (a ⊔ m ⊔ ℓ ⊔ ℓ′) where
    infixr 7 _*ₘ_
    open LeftDefs A ≤ₘ
    field
      _*ₘ_ : Opₗ A M
      *ₘ-mono : Monotonic ≤ _*ₘ_

  record MonoOpᵣ {a m ℓ ℓ′} {A : Set a} {M : Set m}
                 (≤ : Rel A ℓ′) (≤ₘ : Rel M ℓ) : Set (a ⊔ m ⊔ ℓ ⊔ ℓ′) where
    infixr 7 _ₘ*_
    open RightDefs A ≤ₘ
    field
      _ₘ*_ : Opᵣ A M
      ₘ*-mono : Monotonic ≤ _ₘ*_

  --

  -- TODO: does parametrising over a Proset and a MonoOp₂ improve performance?
  record IsSkewMonoid {c ℓ} {C : Set c} (≤ : Rel C ℓ)
                      (ε : C) (∙ : Op₂ C) : Set (c ⊔ ℓ) where
    open Defs ≤
    field
      identity : Identity ε ∙
      assoc : Associative ∙

  -- Same as IsCommutativeMonoid, except without a _≈_.
  record IsSkewCommutativeMonoid {c ℓ} {C : Set c} (≤ : Rel C ℓ)
                                 (ε : C) (∙ : Op₂ C) : Set (c ⊔ ℓ) where
    open Defs ≤
    field
      isLeftSkewMonoid : IsSkewMonoid ≤ ε ∙
      isRightSkewMonoid : IsSkewMonoid (flip ≤) ε ∙
      comm : Commutative ∙
    open IsSkewMonoid isLeftSkewMonoid public
      renaming (identity to identity-→; assoc to assoc-→)
    open IsSkewMonoid isRightSkewMonoid public
      renaming (identity to identity-←; assoc to assoc-←)

  record IsSkewSemiring {c ℓ} {C : Set c} (≤ : Rel C ℓ)
                        (0# : C) (+ : Op₂ C) (1# : C) (* : Op₂ C)
                        : Set (c ⊔ ℓ) where
    open Defs ≤
    field
      +-isSkewCommutativeMonoid : IsSkewCommutativeMonoid ≤ 0# +
      *-isSkewMonoid : IsSkewMonoid ≤ 1# *
      annihil : Annihilates 0# *
      distrib : Distributes + *
    module + = IsSkewCommutativeMonoid +-isSkewCommutativeMonoid
    module * = IsSkewMonoid *-isSkewMonoid

  --

  record SkewMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      proset : Proset c ℓ
    open Proset proset public
    field
      ε : Carrier
      comp : MonoOp₂ _≤_
    open MonoOp₂ comp
    field
      isSkewMonoid : IsSkewMonoid _≤_ ε _∙_
    open IsSkewMonoid isSkewMonoid public

  record SkewCommutativeMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      proset : Proset c ℓ
    open Proset proset public
    field
      ε : Carrier
      comp : MonoOp₂ _≤_
    open MonoOp₂ comp
    field
      isSkewCommutativeMonoid : IsSkewCommutativeMonoid _≤_ ε _∙_
    open IsSkewCommutativeMonoid isSkewCommutativeMonoid public

    leftSkewMonoid : SkewMonoid c ℓ
    leftSkewMonoid = record
      { proset = proset; comp = comp; isSkewMonoid = isLeftSkewMonoid }

    rightSkewMonoid : SkewMonoid c ℓ
    rightSkewMonoid = record
      { proset = proset ᵒᵖ; comp = comp ᵒᵖ₂
      ; isSkewMonoid = isRightSkewMonoid
      }

  record SkewSemiring c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      proset : Proset c ℓ
    open Proset proset public
    field
      0# : Carrier
      plus : MonoOp₂ _≤_
      1# : Carrier
      mult : MonoOp₂ _≤_
    open MonoOp₂ plus public
      renaming (_∙_ to infix 6 _+_; mono to +-mono)
    open MonoOp₂ mult public
      renaming (_∙_ to infix 7 _*_; mono to *-mono)
    field
      isSkewSemiring : IsSkewSemiring _≤_ 0# _+_ 1# _*_
    open IsSkewSemiring isSkewSemiring public

  --

  record SkewSemiringMor {r rℓ s sℓ} (R : SkewSemiring r rℓ)
                                     (S : SkewSemiring s sℓ)
                         : Set (r ⊔ rℓ ⊔ s ⊔ sℓ) where
    private
      module R = SkewSemiring R
      module S = SkewSemiring S
      open S using (_≤_)
    field
      prosetMor : ProsetMor R.proset S.proset
    open ProsetMor prosetMor public
    field
      hom-0# : apply R.0# ≤ S.0#
      hom-+ : ∀ x y → apply (x R.+ y) ≤ apply x S.+ apply y
      hom-1# : apply R.1# ≤ S.1#
      hom-* : ∀ x y → apply (x R.* y) ≤ apply x S.* apply y

  --

  module _ {cr ℓr cs ℓs} (R : SkewSemiring cr ℓr) (S : SkewSemiring cs ℓs) where
    private
      module R = SkewSemiring R
      module S = SkewSemiring S

    record IsSkewBisemimodule
      {cm ℓm} {M : Set cm} (≤ : Rel M ℓm) (0ₘ : M) (+ₘ : Op₂ M)
      (*ₘ : Opₗ R.Carrier M) (ₘ* : Opᵣ S.Carrier M) : Set (cr ⊔ cs ⊔ cm ⊔ ℓm)
      where
      private
        module LD = LeftDefs R.Carrier ≤
        module RD = RightDefs S.Carrier ≤
        module BD = BothDefs R.Carrier S.Carrier ≤
      field
        isSkewCommutativeMonoid : IsSkewCommutativeMonoid ≤ 0ₘ +ₘ
      open IsSkewCommutativeMonoid isSkewCommutativeMonoid public
        renaming ( identity-→ to +ₘ-identity-→
                 ; assoc-→ to +ₘ-assoc-→
                 ; identity-← to +ₘ-identity-←
                 ; assoc-← to +ₘ-assoc-←
                 ; comm to +ₘ-comm
                 ; isLeftSkewMonoid to +ₘ-isLeftSkewMonoid
                 ; isRightSkewMonoid to +ₘ-isRightSkewMonoid
                 )
      field  -- left action
        *ₘ-identityˡ : LD.LeftIdentity R.1# *ₘ
        *ₘ-assoc : LD.Associative R._*_ *ₘ
        *ₘ-annihil : LD.Annihilates R.0# 0ₘ *ₘ
        *ₘ-distrib : LD.Distributes R._+_ +ₘ *ₘ
      field  -- right action
        ₘ*-identityʳ : RD.RightIdentity S.1# ₘ*
        ₘ*-assoc : RD.Associative S._*_ ₘ*
        ₘ*-annihil : RD.Annihilates S.0# 0ₘ ₘ*
        ₘ*-distrib : RD.Distributes S._+_ +ₘ ₘ*
      field  -- both
        *ₘ-ₘ*-assoc : BD.Associative *ₘ ₘ*

    record SkewBisemimodule cm ℓm : Set (cr ⊔ cs ⊔ ℓr ⊔ ℓs ⊔ suc (cm ⊔ ℓm))
      where
      field
        proset : Proset cm ℓm
      open Proset proset public
        renaming (Carrier to Carrierₘ; _≤_ to _≤ₘ_)
      field
        0ₘ : Carrierₘ
        plusₘ : MonoOp₂ _≤ₘ_
        left-scale : MonoOpₗ R._≤_ _≤ₘ_
        right-scale : MonoOpᵣ S._≤_ _≤ₘ_
      open MonoOp₂ plusₘ public
        renaming (_∙_ to infix 6 _+ₘ_; mono to +ₘ-mono)
      open MonoOpₗ left-scale public
      open MonoOpᵣ right-scale public
      field
        isSkewBisemimodule : IsSkewBisemimodule _≤ₘ_ 0ₘ _+ₘ_ _*ₘ_ _ₘ*_
      open IsSkewBisemimodule isSkewBisemimodule public

  module _ {cr₀ ℓr₀ cs₀ ℓs₀ cr₁ ℓr₁ cs₁ ℓs₁}
    {R₀ : SkewSemiring cr₀ ℓr₀} {S₀ : SkewSemiring cs₀ ℓs₀}
    {R₁ : SkewSemiring cr₁ ℓr₁} {S₁ : SkewSemiring cs₁ ℓs₁}
    where

    record SkewBisemimoduleMor {cm₀ ℓm₀ cm₁ ℓm₁}
      (r : SkewSemiringMor R₀ R₁)
      (s : SkewSemiringMor S₀ S₁)
      (M₀ : SkewBisemimodule R₀ S₀ cm₀ ℓm₀)
      (M₁ : SkewBisemimodule R₁ S₁ cm₁ ℓm₁)
      : Set (cr₀ ⊔ cs₀ ⊔ cm₀ ⊔ ℓm₀ ⊔ cm₁ ⊔ ℓm₁)
      where
      private
        module r = SkewSemiringMor r
        module s = SkewSemiringMor s
        module M₀ = SkewBisemimodule M₀
        module M₁ = SkewBisemimodule M₁
      field
        prosetMor : ProsetMor M₀.proset M₁.proset
      open ProsetMor prosetMor public
      field
        hom-0ₘ : apply M₀.0ₘ M₁.≤ₘ M₁.0ₘ
        hom-+ₘ : ∀ x y → apply (x M₀.+ₘ y) M₁.≤ₘ apply x M₁.+ₘ apply y
        hom-*ₘ : ∀ x y → apply (x M₀.*ₘ y) M₁.≤ₘ r.apply x M₁.*ₘ apply y
        hom-ₘ* : ∀ x y → apply (x M₀.ₘ* y) M₁.≤ₘ apply x M₁.ₘ* s.apply y
