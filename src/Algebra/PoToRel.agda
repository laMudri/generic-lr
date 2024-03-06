{-# OPTIONS --safe --without-K --postfix-projections #-}

module Algebra.PoToRel where

  open import Algebra
  open import Algebra.Po
  open import Algebra.Relational
  open import Function.Base
  open import Level
  open import Relation.Binary

  private
    variable
      c ℓ₁ ℓ₂ cr ℓr₁ ℓr₂ cm ℓm₁ ℓm₂ : Level

  module _
    {C : Set c} {_≈_ : Rel C ℓ₁} {_≤_ : Rel C ℓ₂} {ε : C} {_∙_ : Op₂ C}
    where

    isPoMonoid-to-isRelMonoid :
      IsPoMonoid _≈_ _≤_ ε _∙_ → IsRelMonoid _≤_ (_≤ ε) (λ z x y → z ≤ (x ∙ y))
    isPoMonoid-to-isRelMonoid X = record
      { isLeftSkewRelMonoid = record
        { identityˡ→ = λ (x0 , zxy) →
          ≤-trans zxy (≤-trans (∙-monoˡ x0) (≤-reflexive (identityˡ _)))
        ; identityʳ← = λ zx →
          ≤-trans zx (≤-reflexive (sym (identityʳ _))) , ≤-refl
        ; assoc→ = λ (w+x , wx+y) →
          ≤-trans wx+y (≤-trans (∙-monoˡ w+x) (≤-reflexive (assoc _ _ _)))
          , ≤-refl
        }
      ; isRightSkewRelMonoid = record
        { identityˡ← = λ zy →
          ≤-refl , ≤-trans zy (≤-reflexive (sym (identityˡ _)))
        ; identityʳ→ = λ (zxy , y0) →
          ≤-trans zxy (≤-trans (∙-monoʳ y0) (≤-reflexive (identityʳ _)))
        ; assoc← = λ (w+xy , x+y) →
          ≤-refl ,
          ≤-trans w+xy (≤-trans (∙-monoʳ x+y) (≤-reflexive (sym (assoc _ _ _))))
        }
      } where open IsPoMonoid X

    isPoCommutativeMonoid-to-isCommutativeRelMonoid :
      IsPoCommutativeMonoid _≈_ _≤_ ε _∙_ →
      IsCommutativeRelMonoid _≤_ (_≤ ε) (λ z x y → z ≤ (x ∙ y))
    isPoCommutativeMonoid-to-isCommutativeRelMonoid X = record
      { isRelMonoid = isPoMonoid-to-isRelMonoid isPoMonoid
      ; comm = λ xyz → ≤-trans xyz (≤-reflexive (comm _ _))
      }
      where open IsPoCommutativeMonoid X

  poCommutativeMonoid-to-commutativeRelMonoid :
    PoCommutativeMonoid c ℓ₁ ℓ₂ → CommutativeRelMonoid c ℓ₂
  poCommutativeMonoid-to-commutativeRelMonoid X = record
    { Carrier = Carrier
    ; _≤_ = _≤_
    ; _≤ε = _≤ ε
    ; _≤[_∙_] = λ z x y → z ≤ x ∙ y
    ; isProset = isProset
    ; ε-mono = ≤-trans
    ; ∙-mono = λ xx yy zz xyz → ≤-trans xx (≤-trans xyz (∙-mono yy zz))
    ; isCommutativeRelMonoid =
      isPoCommutativeMonoid-to-isCommutativeRelMonoid isPoCommutativeMonoid
    } where open PoCommutativeMonoid X

  poSemiring-to-relSemiring : PoSemiring c ℓ₁ ℓ₂ → RelSemiring c ℓ₂
  poSemiring-to-relSemiring X = record
    { Carrier = Carrier
    ; _≤_ = _≤_
    ; _≤0 = _≤ 0#
    ; _≤[_+_] = λ x y z → x ≤ y + z
    ; _≤1 = _≤ 1#
    ; _≤[_*_] = λ x y z → x ≤ y * z
    ; isProset = isProset
    ; 0-mono = ≤-trans
    ; +-mono = λ xx yy zz xyz → ≤-trans xx (≤-trans xyz (+-mono yy zz))
    ; 1-mono = ≤-trans
    ; *-mono = λ xx yy zz xyz → ≤-trans xx (≤-trans xyz (*-mono yy zz))
    ; isRelSemiring = record
      { +-isCommutativeRelMonoid =
        isPoCommutativeMonoid-to-isCommutativeRelMonoid +-isPoCommutativeMonoid
      ; *-isRelMonoid = isPoMonoid-to-isRelMonoid *-isPoMonoid
      ; annihilˡ→ = λ (x0 , zxy) →
        ≤-trans zxy (≤-trans (*-monoˡ x0) (≤-reflexive (annihilˡ _)))
      ; annihilˡ← = λ z0 →
        ≤-refl , ≤-trans z0 (≤-reflexive (sym (annihilˡ _)))
      ; annihilʳ→ = λ (zxy , y0) →
        ≤-trans zxy (≤-trans (*-monoʳ y0) (≤-reflexive (annihilʳ _)))
      ; annihilʳ← = λ z0 →
        ≤-trans z0 (≤-reflexive (sym (annihilʳ _))) , ≤-refl
      ; distribˡ→ = λ (w+x , wx*y) →
        ≤-refl ↘,
        ≤-trans wx*y (≤-trans (*-monoˡ w+x) (≤-reflexive (distribˡ _ _ _)))
        ,↙ ≤-refl
      ; distribˡ← = λ (w*y ↘, wy+xy ,↙ x*y) →
        ≤-refl , ≤-trans wy+xy
          (≤-trans (+-mono w*y x*y) (≤-reflexive (sym (distribˡ _ _ _))))
      ; distribʳ→ = λ (w*xy , x+y) →
        ≤-refl ↘,
        ≤-trans w*xy (≤-trans (*-monoʳ x+y) (≤-reflexive (distribʳ _ _ _)))
        ,↙ ≤-refl
      ; distribʳ← = λ (w*x ↘, wx+wy ,↙ w*y) →
        ≤-trans wx+wy
          (≤-trans (+-mono w*x w*y) (≤-reflexive (sym (distribʳ _ _ _))))
        , ≤-refl
      }
    } where open PoSemiring X

  poSemiring-to-fRelSemiring : PoSemiring c ℓ₁ ℓ₂ → FRelSemiring c ℓ₂
  poSemiring-to-fRelSemiring X = record
    { isProset = isProset
    ; 0-mono = 0-mono
    ; +-mono = +-mono
    ; 1-mono = 1-mono
    ; *-mono = *-mono
    ; isFRelSemiring = record
      { isRelSemiring = isRelSemiring
      ; 0-func = record { holds = X.≤-refl ; unique = id }
      ; +-func = λ x y → record { holds = X.≤-refl ; unique = id }
      ; 1-func = record { holds = X.≤-refl ; unique = id }
      ; *-func = λ x y → record { holds = X.≤-refl ; unique = id }
      }
    }
    where
    module X = PoSemiring X
    open RelSemiring (poSemiring-to-relSemiring X)

  poLeftSemimodule-to-relLeftSemimodule : {R : PoSemiring cr ℓr₁ ℓr₂} →
    PoLeftSemimodule R cm ℓm₁ ℓm₂ →
    RelLeftSemimodule (poSemiring-to-relSemiring R) cm ℓm₂
  poLeftSemimodule-to-relLeftSemimodule {R = R} X = record
    { Carrierₘ = Carrierₘ
    ; _≤ₘ_ = _≤ₘ_
    ; _≤0ₘ = _≤ₘ 0ₘ
    ; _≤[_+ₘ_] = λ w u v → w ≤ₘ u +ₘ v
    ; _≤[_*ₘ_] = λ v r u → v ≤ₘ r *ₘ u
    ; isProset = ≤ₘ-isProset
    ; 0ₘ-mono = ≤ₘ-trans
    ; +ₘ-mono = λ ww uu vv wuv → ≤ₘ-trans ww (≤ₘ-trans wuv (+ₘ-mono uu vv))
    ; *ₘ-mono = λ vv rr uu vru → ≤ₘ-trans vv (≤ₘ-trans vru (*ₘ-mono rr uu))
    ; isRelLeftSemimodule = record
      { +ₘ-isCommutativeRelMonoid =
        isPoCommutativeMonoid-to-isCommutativeRelMonoid +ₘ-isPoCommutativeMonoid
      ; *ₘ-identity→ = λ (r1 , vru) →
        ≤ₘ-trans vru (≤ₘ-trans (*ₘ-monoˡ r1) (≤ₘ-reflexive (*ₘ-identity _)))
      ; *ₘ-identity← = λ vu →
        R.≤-refl , ≤ₘ-trans vu (≤ₘ-reflexive (≈ₘ-sym (*ₘ-identity _)))
      ; *ₘ-assoc→ = λ (r*s , rs*u) →
        ≤ₘ-trans rs*u (≤ₘ-trans (*ₘ-monoˡ r*s) (≤ₘ-reflexive (*ₘ-assoc _ _ _)))
        , ≤ₘ-refl
      ; *ₘ-assoc← = λ (r*su , s*u) →
        R.≤-refl ,
        ≤ₘ-trans r*su
          (≤ₘ-trans (*ₘ-monoʳ s*u) (≤ₘ-reflexive (≈ₘ-sym (*ₘ-assoc _ _ _))))
      ; *ₘ-annihilˡ→ = λ (r0 , vru) →
        ≤ₘ-trans vru (≤ₘ-trans (*ₘ-monoˡ r0) (≤ₘ-reflexive (*ₘ-annihilˡ _)))
      ; *ₘ-annihilˡ← = λ v0 →
        R.≤-refl , ≤ₘ-trans v0 (≤ₘ-reflexive (≈ₘ-sym (*ₘ-annihilˡ _)))
      ; *ₘ-annihilʳ→ = λ (vru , 0#) →
        ≤ₘ-trans vru (≤ₘ-trans (*ₘ-monoʳ 0#) (≤ₘ-reflexive (*ₘ-annihilʳ _)))
      ; *ₘ-annihilʳ← = λ v0 →
        ≤ₘ-trans v0 (≤ₘ-reflexive (≈ₘ-sym (*ₘ-annihilʳ _))) , ≤ₘ-refl
      ; *ₘ-distribˡ→ = λ (r+s , rs*u) →
        ≤ₘ-refl ↘,
        ≤ₘ-trans rs*u
          (≤ₘ-trans (*ₘ-monoˡ r+s) (≤ₘ-reflexive (*ₘ-distribˡ _ _ _)))
        ,↙ ≤ₘ-refl
      ; *ₘ-distribˡ← = λ (r*u ↘, ru+su ,↙ s*u) →
        R.≤-refl ,
        ≤ₘ-trans ru+su (≤ₘ-trans (+ₘ-mono r*u s*u)
          (≤ₘ-reflexive (≈ₘ-sym (*ₘ-distribˡ _ _ _))))
      ; *ₘ-distribʳ→ = λ (r*uv , u+v) →
        ≤ₘ-refl ↘,
        ≤ₘ-trans r*uv (≤ₘ-trans (*ₘ-monoʳ u+v) (≤ₘ-reflexive (*ₘ-distribʳ _ _ _)))
        ,↙ ≤ₘ-refl
      ; *ₘ-distribʳ← = λ (r*u ↘, ru+rv ,↙ r*v) →
        ≤ₘ-trans ru+rv (≤ₘ-trans (+ₘ-mono r*u r*v)
          (≤ₘ-reflexive (≈ₘ-sym (*ₘ-distribʳ _ _ _))))
        , ≤ₘ-refl
      }
    } where module R = PoSemiring R; open PoLeftSemimodule X

  poLeftSemimodule-to-fRelLeftSemimodule : {R : PoSemiring cr ℓr₁ ℓr₂} →
    PoLeftSemimodule R cm ℓm₁ ℓm₂ →
    FRelLeftSemimodule (poSemiring-to-fRelSemiring R) cm ℓm₂
  poLeftSemimodule-to-fRelLeftSemimodule {R = R} X = record
    { isProset = isProset
    ; 0ₘ-mono = 0ₘ-mono
    ; +ₘ-mono = +ₘ-mono
    ; *ₘ-mono = *ₘ-mono
    ; isFRelLeftSemimodule = record
      { isRelLeftSemimodule = isRelLeftSemimodule
      ; 0ₘ-func = record { holds = X.≤ₘ-refl ; unique = id }
      ; +ₘ-func = λ u v → record { holds = X.≤ₘ-refl ; unique = id }
      ; *ₘ-func = λ r v → record { holds = X.≤ₘ-refl ; unique = id }
      }
    }
    where
    module X = PoLeftSemimodule X
    open RelLeftSemimodule (poLeftSemimodule-to-relLeftSemimodule X)
