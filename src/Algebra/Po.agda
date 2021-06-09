{-# OPTIONS --without-K --safe --postfix-projections #-}

module Algebra.Po where

  open import Algebra hiding
    ( LeftIdentity; Associative; LeftZero; RightZero; _DistributesOverˡ_
    ; _DistributesOverʳ_
    )
  import Algebra.Module.Definitions.Left as LeftDefs
  open import Algebra.Skew
  open import Data.Product
  open import Function.Base using (flip)
  open import Level using (_⊔_; suc)
  open import Relation.Binary
  import Relation.Binary.Reasoning.Setoid as SetoidR

  record RawPoset c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    infix 4 _≈_ _≤_
    field
      Carrier : Set c
      _≈_ : Rel Carrier ℓ₁
      _≤_ : Rel Carrier ℓ₂

  record RawPoSemiring c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    infix 6 _+_
    infix 7 _*_
    field
      rawPoset : RawPoset c ℓ₁ ℓ₂
    open RawPoset rawPoset public
    field
      0# : Carrier
      _+_ : Op₂ Carrier
      1# : Carrier
      _*_ : Op₂ Carrier

  -- Structures

  record IsPoMonoid
    {c ℓ₁ ℓ₂} {Carrier : Set c} (≈ : Rel Carrier ℓ₁) (≤ : Rel Carrier ℓ₂)
    (ε : Carrier) (∙ : Op₂ Carrier) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isPartialOrder : IsPartialOrder ≈ ≤
      isMonoid : IsMonoid ≈ ∙ ε
      ∙-mono : Congruent₂ ≤ ∙

    open IsPartialOrder isPartialOrder public renaming
      ( refl to ≤-refl; reflexive to ≤-reflexive; trans to ≤-trans
      ; antisym to ≤-antisym
      )
    open IsMonoid isMonoid public

    ∙-monoˡ : RightCongruent ≤ ∙
    ∙-monoˡ xx = ∙-mono xx ≤-refl
    ∙-monoʳ : LeftCongruent ≤ ∙
    ∙-monoʳ yy = ∙-mono ≤-refl yy

    isProset : IsProset ≤
    isProset = record { refl = ≤-refl ; trans = ≤-trans }

    isSkewMonoidˡ : IsSkewMonoid ≤ ε ∙
    isSkewMonoidˡ = record
      { identity = λ where
        .proj₁ x → ≤-reflexive (identity .proj₁ x)
        .proj₂ x → ≤-reflexive (sym (identity .proj₂ x))
      ; assoc = λ x y z → ≤-reflexive (assoc x y z)
      }

    isSkewMonoidʳ : IsSkewMonoid (flip ≤) ε ∙
    isSkewMonoidʳ = record
      { identity = λ where
        .proj₁ x → ≤-reflexive (sym (identity .proj₁ x))
        .proj₂ x → ≤-reflexive (identity .proj₂ x)
      ; assoc = λ x y z → ≤-reflexive (sym (assoc x y z))
      }

  record IsPoCommutativeMonoid
    {c ℓ₁ ℓ₂} {Carrier : Set c} (≈ : Rel Carrier ℓ₁) (≤ : Rel Carrier ℓ₂)
    (ε : Carrier) (∙ : Op₂ Carrier) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isPoMonoid : IsPoMonoid ≈ ≤ ε ∙
      comm : Commutative ≈ ∙
    open IsPoMonoid isPoMonoid public

    isCommutativeMonoid : IsCommutativeMonoid ≈ ∙ ε
    isCommutativeMonoid = record { isMonoid = isMonoid ; comm = comm }

    isSkewCommutativeMonoid : IsSkewCommutativeMonoid ≤ ε ∙
    isSkewCommutativeMonoid = record
      { isLeftSkewMonoid = isSkewMonoidˡ
      ; isRightSkewMonoid = isSkewMonoidʳ
      ; comm = λ x y → ≤-reflexive (comm x y)
      }

  record IsPoSemiring
    {c ℓ₁ ℓ₂} {Carrier : Set c} (≈ : Rel Carrier ℓ₁) (≤ : Rel Carrier ℓ₂)
    (0# : Carrier) (+ : Op₂ Carrier) (1# : Carrier) (* : Op₂ Carrier)
    : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isPartialOrder : IsPartialOrder ≈ ≤
      isSemiring : IsSemiring ≈ + * 0# 1#
      +-mono : Congruent₂ ≤ +
      *-mono : Congruent₂ ≤ *

    open IsPartialOrder isPartialOrder public renaming
      (refl to ≤-refl; reflexive to ≤-reflexive; trans to ≤-trans)
    open IsSemiring isSemiring public renaming
      ( zeroˡ to annihilˡ; zeroʳ to annihilʳ
      ; distribʳ to distribˡ; distribˡ to distribʳ
      )

    +-isPoCommutativeMonoid : IsPoCommutativeMonoid ≈ ≤ 0# +
    +-isPoCommutativeMonoid = record
      { isPoMonoid = record
        { isPartialOrder = isPartialOrder
        ; isMonoid = +-isMonoid
        ; ∙-mono = +-mono
        }
      ; comm = +-comm
      }
    open IsPoCommutativeMonoid +-isPoCommutativeMonoid public
      using (isProset) renaming
      ( isPoMonoid to +-isPoMonoid
      ; isSkewCommutativeMonoid to +-isSkewCommutativeMonoid
      ; ∙-monoˡ to +-monoˡ; ∙-monoʳ to +-monoʳ
      )

    *-isPoMonoid : IsPoMonoid ≈ ≤ 1# *
    *-isPoMonoid = record
      { isPartialOrder = isPartialOrder
      ; isMonoid = *-isMonoid
      ; ∙-mono = *-mono
      }
    open IsPoMonoid *-isPoMonoid public using () renaming
      ( isSkewMonoidˡ to *-isSkewMonoidˡ
      ; ∙-monoˡ to *-monoˡ; ∙-monoʳ to *-monoʳ
      )

    isSkewSemiring : IsSkewSemiring ≤ 0# + 1# *
    isSkewSemiring = record
      { +-isSkewCommutativeMonoid = +-isSkewCommutativeMonoid
      ; *-isSkewMonoid = *-isSkewMonoidˡ
      ; annihil = λ where
        .proj₁ x → ≤-reflexive (zero .proj₁ x)
        .proj₂ x → ≤-reflexive (sym (zero .proj₂ x))
      ; distrib = λ where
        .proj₁ x y z → ≤-reflexive (distrib .proj₂ z x y)
        .proj₂ x y z → ≤-reflexive (sym (distrib .proj₁ x y z))
      }
    open IsSkewSemiring isSkewSemiring public
      hiding (+-isSkewCommutativeMonoid; *-isSkewMonoid)
      renaming (annihil to ≤-annihil; distrib to ≤-distrib)

  -- Bundles

  record PoMonoid c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    infix 4 _≈_ _≤_
    infix 5 _∙_
    field
      Carrier : Set c
      _≈_ : Rel Carrier ℓ₁
      _≤_ : Rel Carrier ℓ₂
      ε : Carrier
      _∙_ : Op₂ Carrier
      isPoMonoid : IsPoMonoid _≈_ _≤_ ε _∙_

    open IsPoMonoid isPoMonoid public
    poset : Poset c ℓ₁ ℓ₂
    poset = record { isPartialOrder = isPartialOrder }
    monoid : Monoid c ℓ₁
    monoid = record { isMonoid = isMonoid }

    skewMonoidˡ : SkewMonoid c ℓ₂
    skewMonoidˡ = record
      { proset = record
        { Carrier = Carrier
        ; _≤_ = _≤_
        ; isProset = record { refl = ≤-refl ; trans = ≤-trans }
        }
      ; ε = ε
      ; comp = record { _∙_ = _∙_; mono = ∙-mono }
      ; isSkewMonoid = isSkewMonoidˡ
      }
    open SkewMonoid skewMonoidˡ public using (proset; comp)

    skewMonoidʳ : SkewMonoid c ℓ₂
    skewMonoidʳ = record
      { proset = proset ᵒᵖ
      ; ε = ε
      ; comp = comp ᵒᵖ₂
      ; isSkewMonoid = isSkewMonoidʳ
      }

  record PoCommutativeMonoid c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    infix 4 _≈_ _≤_
    infix 5 _∙_
    field
      Carrier : Set c
      _≈_ : Rel Carrier ℓ₁
      _≤_ : Rel Carrier ℓ₂
      ε : Carrier
      _∙_ : Op₂ Carrier
      isPoCommutativeMonoid : IsPoCommutativeMonoid _≈_ _≤_ ε _∙_

    open IsPoCommutativeMonoid isPoCommutativeMonoid public
    poMonoid : PoMonoid c ℓ₁ ℓ₂
    poMonoid = record { isPoMonoid = isPoMonoid }
    open PoMonoid poMonoid public
      using (poset; monoid; skewMonoidˡ; skewMonoidʳ; proset; comp)

    commutativeMonoid : CommutativeMonoid c ℓ₁
    commutativeMonoid = record { isCommutativeMonoid = isCommutativeMonoid }

    inter : Interchangable _≈_ _∙_ _∙_
    inter w x y z = begin
      (w ∙ x) ∙ (y ∙ z)  ≈⟨ assoc _ _ _ ⟩
      w ∙ (x ∙ (y ∙ z))  ≈˘⟨ ∙-cong refl (assoc _ _ _) ⟩
      w ∙ ((x ∙ y) ∙ z)  ≈⟨ ∙-cong refl (∙-cong (comm _ _) refl) ⟩
      w ∙ ((y ∙ x) ∙ z)  ≈⟨ ∙-cong refl (assoc _ _ _) ⟩
      w ∙ (y ∙ (x ∙ z))  ≈˘⟨ assoc _ _ _ ⟩
      (w ∙ y) ∙ (x ∙ z)  ∎
      where open SetoidR setoid

    skewCommutativeMonoid : SkewCommutativeMonoid c ℓ₂
    skewCommutativeMonoid = record
      { proset = proset
      ; ε = ε
      ; comp = comp
      ; isSkewCommutativeMonoid = isSkewCommutativeMonoid
      }

  record PoSemiring c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    infix 4 _≈_ _≤_
    infix 6 _+_
    infix 7 _*_
    field
      Carrier : Set c
      _≈_ : Rel Carrier ℓ₁
      _≤_ : Rel Carrier ℓ₂
      0# : Carrier
      _+_ : Op₂ Carrier
      1# : Carrier
      _*_ : Op₂ Carrier
      isPoSemiring : IsPoSemiring _≈_ _≤_ 0# _+_ 1# _*_
    open IsPoSemiring isPoSemiring public

    +-poCommutativeMonoid : PoCommutativeMonoid c ℓ₁ ℓ₂
    +-poCommutativeMonoid = record
      { isPoCommutativeMonoid = +-isPoCommutativeMonoid }
    open PoCommutativeMonoid +-poCommutativeMonoid public
      using (poset; proset) renaming
      ( poMonoid to +-poMonoid; skewMonoidˡ to +-skewMonoidˡ
      ; skewMonoidʳ to +-skewMonoidʳ; comp to plus; inter to +-inter
      )

    *-poMonoid : PoMonoid c ℓ₁ ℓ₂
    *-poMonoid = record { isPoMonoid = *-isPoMonoid }
    open PoMonoid *-poMonoid public using () renaming
      ( skewMonoidˡ to *-skewMonoidˡ; skewMonoidʳ to *-skewMonoidʳ; comp to mult
      )

    skewSemiring : SkewSemiring c ℓ₂
    skewSemiring = record
      { proset = proset
      ; plus = plus
      ; mult = mult
      ; isSkewSemiring = isSkewSemiring
      }
    open SkewSemiring skewSemiring public
      using (rawSkewSemiring; module +; module *)

    rawPoSemiring : RawPoSemiring c ℓ₁ ℓ₂
    rawPoSemiring = record
      { rawPoset = record { Carrier = Carrier ; _≈_ = _≈_ ; _≤_ = _≤_ }
      ; 0# = 0#
      ; _+_ = _+_
      ; 1# = 1#
      ; _*_ = _*_
      }

  record PoSemiringMor {r rℓ₁ rℓ₂ s sℓ₁ sℓ₂}
    (R : PoSemiring r rℓ₁ rℓ₂) (S : PoSemiring s sℓ₁ sℓ₂)
    : Set (r ⊔ rℓ₁ ⊔ rℓ₂ ⊔ s ⊔ sℓ₁ ⊔ sℓ₂) where
    private
      module R = PoSemiring R
      module S = PoSemiring S
      open S using (_≈_)
    field
      hom : R.Carrier → S.Carrier
      hom-cong : ∀ {x y} → x R.≈ y → hom x S.≈ hom y
      hom-mono : ∀ {x y} → x R.≤ y → hom x S.≤ hom y
      hom-0# : hom R.0# ≈ S.0#
      hom-+ : ∀ x y → hom (x R.+ y) ≈ hom x S.+ hom y
      hom-1# : hom R.1# ≈ S.1#
      hom-* : ∀ x y → hom (x R.* y) ≈ hom x S.* hom y

  --

  module _ {cr ℓr₁ ℓr₂} (R : PoSemiring cr ℓr₁ ℓr₂) where
    private
      module R = PoSemiring R

    record IsPoLeftSemimodule
      {cm ℓm₁ ℓm₂} {M : Set cm} (≈ : Rel M ℓm₁) (≤ : Rel M ℓm₂)
      (0ₘ : M) (+ₘ : Op₂ M) (*ₘ : Opₗ R.Carrier M)
      : Set (cr ⊔ ℓr₁ ⊔ ℓr₂ ⊔ cm ⊔ ℓm₁ ⊔ ℓm₂) where
      open LeftDefs R.Carrier ≈
      field
        +ₘ-isPoCommutativeMonoid : IsPoCommutativeMonoid ≈ ≤ 0ₘ +ₘ
        *ₘ-cong : LeftDefs.Congruent R.Carrier ≈ R._≈_ *ₘ
        *ₘ-mono : LeftDefs.Congruent R.Carrier ≤ R._≤_ *ₘ
        *ₘ-identity : LeftIdentity R.1# *ₘ
        *ₘ-assoc : Associative R._*_ *ₘ
        *ₘ-annihilˡ : LeftZero R.0# 0ₘ *ₘ
        *ₘ-annihilʳ : RightZero 0ₘ *ₘ
        *ₘ-distribˡ : *ₘ DistributesOverʳ R._+_ ⟶ +ₘ
        *ₘ-distribʳ : *ₘ DistributesOverˡ +ₘ
      open IsPoCommutativeMonoid +ₘ-isPoCommutativeMonoid public renaming
        ( identity to +ₘ-identity; identityʳ to +ₘ-identityʳ
        ; identityˡ to +ₘ-identityˡ; assoc to +ₘ-assoc; comm to +ₘ-comm
        ; ∙-cong to +ₘ-cong; ∙-monoˡ to +ₘ-monoˡ; ∙-monoʳ to +ₘ-monoʳ
        ; ∙-mono to +ₘ-mono
        ; ≤-refl to ≤ₘ-refl; ≤-trans to ≤ₘ-trans
        ; ≤-antisym to ≤ₘ-antisym; ≤-reflexive to ≤ₘ-reflexive
        ; refl to ≈ₘ-refl; trans to ≈ₘ-trans; sym to ≈ₘ-sym
        ; reflexive to ≈ₘ-reflexive
        ; isPreorder to ≤ₘ-isPreorder; isPartialOrder to ≤ₘ-isPartialOrder
        ; isProset to ≤ₘ-isProset; isEquivalence to ≈ₘ-isEquivalence
        ; isPoMonoid to +ₘ-isPoMonoid; isMonoid to +ₘ-isMonoid
        ; isCommutativeMonoid to +ₘ-isCommutativeMonoid
        ; isMagma to +ₘ-isMagma; isSemigroup to +ₘ-isSemigroup
        )

      *ₘ-monoˡ : ∀ {r r′ u} → r R.≤ r′ → ≤ (*ₘ r u) (*ₘ r′ u)
      *ₘ-monoˡ rr = *ₘ-mono rr ≤ₘ-refl
      *ₘ-monoʳ : ∀ {r u u′} → ≤ u u′ → ≤ (*ₘ r u) (*ₘ r u′)
      *ₘ-monoʳ uu = *ₘ-mono R.≤-refl uu

    record PoLeftSemimodule cm ℓm₁ ℓm₂
      : Set (cr ⊔ ℓr₁ ⊔ ℓr₂ ⊔ suc (cm ⊔ ℓm₁ ⊔ ℓm₂)) where
      infix 4 _≈ₘ_
      infix 4 _≤ₘ_
      infix 6 _+ₘ_
      infixr 7 _*ₘ_
      field
        Carrierₘ : Set cm
        _≈ₘ_ : Rel Carrierₘ ℓm₁
        _≤ₘ_ : Rel Carrierₘ ℓm₂
        0ₘ : Carrierₘ
        _+ₘ_ : Op₂ Carrierₘ
        _*ₘ_ : Opₗ R.Carrier Carrierₘ
        isPoLeftSemimodule : IsPoLeftSemimodule _≈ₘ_ _≤ₘ_ 0ₘ _+ₘ_ _*ₘ_
      open IsPoLeftSemimodule isPoLeftSemimodule public

      +ₘ-poCommutativeMonoid : PoCommutativeMonoid cm ℓm₁ ℓm₂
      +ₘ-poCommutativeMonoid =
        record { isPoCommutativeMonoid = +ₘ-isPoCommutativeMonoid }
      open PoCommutativeMonoid +ₘ-poCommutativeMonoid public using () renaming
        (poMonoid to +ₘ-poMonoid; inter to +ₘ-inter)

  module _ {cr ℓr₁ ℓr₂ cs ℓs₁ ℓs₂}
    {R : PoSemiring cr ℓr₁ ℓr₂} {S : PoSemiring cs ℓs₁ ℓs₂}
    where

    record PoLeftSemimoduleMor {cm ℓm₁ ℓm₂ cn ℓn₁ ℓn₂}
      (r : PoSemiringMor R S)
      (M : PoLeftSemimodule R cm ℓm₁ ℓm₂)
      (N : PoLeftSemimodule S cn ℓn₁ ℓn₂)
      : Set (cr ⊔ cm ⊔ ℓm₁ ⊔ ℓm₂ ⊔ cn ⊔ ℓn₁ ⊔ ℓn₂)
      where
      private
        module r = PoSemiringMor r
        module M = PoLeftSemimodule M
        module N = PoLeftSemimodule N
      field
        hom : M.Carrierₘ → N.Carrierₘ
        hom-cong : ∀ {x y} → x M.≈ₘ y → hom x N.≈ₘ hom y
        hom-mono : ∀ {x y} → x M.≤ₘ y → hom x N.≤ₘ hom y
        hom-0ₘ : hom M.0ₘ N.≈ₘ N.0ₘ
        hom-+ₘ : ∀ x y → hom (x M.+ₘ y) N.≈ₘ hom x N.+ₘ hom y
        hom-*ₘ : ∀ x y → hom (x M.*ₘ y) N.≈ₘ r.hom x N.*ₘ hom y
