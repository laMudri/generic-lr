{-# OPTIONS --without-K --safe --postfix-projections #-}

module Algebra.Skew.Construct.Vector where

  open import Algebra.Skew
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.Product
  open import Data.Product.Relation.Binary.Pointwise.NonDependent
  open import Data.Unit.Polymorphic
  open import Function.Base

  infixl 2 _<*>_

  pure : ∀ {a} {A : Set a} → A → A × A
  pure x = x , x

  _<*>_ : ∀ {a b x y} {A : Set a} {B : Set b} {X : A → Set x} {Y : B → Set y} →
          ((a : A) → X a) × ((b : B) → Y b) →
          ((a , b) : A × B) → X a × Y b
  (f , g) <*> (x , y) = f x , g y

  ⊤-skewBisemimodule :
    ∀ {cr ℓr cs ℓs c ℓ} {R : SkewSemiring cr ℓr} {S : SkewSemiring cs ℓs} →
    SkewBisemimodule R S c ℓ
  ⊤-skewBisemimodule = record
    { proset = record { Carrier = ⊤ ; _≤_ = λ _ _ → ⊤ } }

  ×-skewBisemimodule :
    ∀ {cr ℓr cs ℓs c ℓ} {R : SkewSemiring cr ℓr} {S : SkewSemiring cs ℓs} →
    SkewBisemimodule R S c ℓ → SkewBisemimodule R S c ℓ →
    SkewBisemimodule R S c ℓ
  ×-skewBisemimodule M N = record
    { proset = record
      { Carrier = M.Carrierₘ × N.Carrierₘ
      ; _≤_ = Pointwise M._≤ₘ_ N._≤ₘ_
      ; isProset = record
        { refl = M.refl , N.refl
        ; trans = zip M.trans N.trans
        }
      }
    ; 0ₘ = M.0ₘ , N.0ₘ
    ; plusₘ = record
      { _∙_ = λ x y → (M._+ₘ_ , N._+ₘ_) <*> x <*> y
      ; mono = λ x y → (M.+ₘ-mono , N.+ₘ-mono) <*> x <*> y
      }
    ; left-scale = record
      { _*ₘ_ = λ r x → (M._*ₘ_ , N._*ₘ_) <*> pure r <*> x
      ; *ₘ-mono = λ r x → (M.*ₘ-mono , N.*ₘ-mono) <*> pure r <*> x
      }
    ; right-scale = record
      { _ₘ*_ = λ x s → (M._ₘ*_ , N._ₘ*_) <*> x <*> pure s
      ; ₘ*-mono = λ x s → (M.ₘ*-mono , N.ₘ*-mono) <*> x <*> pure s
      }
    ; isSkewBisemimodule = record
      { isSkewCommutativeMonoid = record
        { isLeftSkewMonoid = record
          { identity =
            (λ x → (pure (proj₁ ∘ +ₘ-identity-→) <*> (M , N)) <*> x)
          , (λ x → (pure (proj₂ ∘ +ₘ-identity-→) <*> (M , N)) <*> x)
          ; assoc = λ x y z → (pure +ₘ-assoc-→ <*> (M , N)) <*> x <*> y <*> z
          }
        ; isRightSkewMonoid = record
          { identity =
            (λ x → (pure (proj₁ ∘ +ₘ-identity-←) <*> (M , N)) <*> x)
          , (λ x → (pure (proj₂ ∘ +ₘ-identity-←) <*> (M , N)) <*> x)
          ; assoc = λ x y z → (pure +ₘ-assoc-← <*> (M , N)) <*> x <*> y <*> z
          }
        ; comm = λ x y → (pure +ₘ-comm <*> (M , N)) <*> x <*> y
        }
      ; *ₘ-identityˡ = λ x → (pure *ₘ-identityˡ <*> (M , N)) <*> x
      ; *ₘ-assoc = λ x y z →
        (pure *ₘ-assoc <*> (M , N)) <*> pure x <*> pure y <*> z
      ; *ₘ-annihil =
        (λ x → (pure (proj₁ ∘ *ₘ-annihil) <*> (M , N)) <*> x)
      , (λ x → (pure (proj₂ ∘ *ₘ-annihil) <*> (M , N)) <*> pure x)
      ; *ₘ-distrib =
        (λ x y z → (pure (proj₁ ∘ *ₘ-distrib) <*> (M , N))
                   <*> pure x <*> pure y <*> z)
      , (λ x y z → (pure (proj₂ ∘ *ₘ-distrib) <*> (M , N))
                   <*> pure x <*> y <*> z)
      ; ₘ*-identityʳ = λ x → (pure ₘ*-identityʳ <*> (M , N)) <*> x
      ; ₘ*-assoc = λ x y z →
        (pure ₘ*-assoc <*> (M , N)) <*> x <*> pure y <*> pure z
      ; ₘ*-annihil =
        (λ x → (pure (proj₁ ∘ ₘ*-annihil) <*> (M , N)) <*> pure x)
      , (λ x → (pure (proj₂ ∘ ₘ*-annihil) <*> (M , N)) <*> x)
      ; ₘ*-distrib = 
        (λ x y z → (pure (proj₁ ∘ ₘ*-distrib) <*> (M , N))
                   <*> x <*> y <*> pure z)
      , (λ x y z → (pure (proj₂ ∘ ₘ*-distrib) <*> (M , N))
                   <*> x <*> pure y <*> pure z)
      ; *ₘ-ₘ*-assoc = λ x y z →
        (pure *ₘ-ₘ*-assoc <*> (M , N)) <*> pure x <*> y <*> pure z
      }
    }
    where
    module M = SkewBisemimodule M
    module N = SkewBisemimodule N
    open SkewBisemimodule

  I-skewBisemimodule :
    ∀ {c ℓ} {R : SkewSemiring c ℓ} → SkewBisemimodule R R c ℓ
  I-skewBisemimodule {R = R} = record
    { proset = proset
    ; 0ₘ = 0#
    ; plusₘ = plus
    ; left-scale = record { _*ₘ_ = _*_ ; *ₘ-mono = *-mono }
    ; right-scale = record { _ₘ*_ = _*_ ; ₘ*-mono = *-mono }
    ; isSkewBisemimodule = record
      { isSkewCommutativeMonoid = +-isSkewCommutativeMonoid
      ; *ₘ-identityˡ = proj₁ *.identity
      ; *ₘ-assoc = *.assoc
      ; *ₘ-annihil = annihil
      ; *ₘ-distrib = distrib
      ; ₘ*-identityʳ = proj₂ *.identity
      ; ₘ*-assoc = *.assoc
      ; ₘ*-annihil = annihil
      ; ₘ*-distrib = distrib
      ; *ₘ-ₘ*-assoc = *.assoc
      }
    } where open SkewSemiring R

  Vector-skewBisemimodule :
    ∀ {c ℓ} (R : SkewSemiring c ℓ) → LTree → SkewBisemimodule R R c ℓ
  Vector-skewBisemimodule R s = record
    { proset = record
      { Carrier = Vector Carrier s
      ; _≤_ = Lift₂ _≤_
      ; isProset = record
        { refl = mk λ _ → refl
        ; trans = λ (mk f) (mk g) → mk λ i → trans (f i) (g i)
        }
      }
    ; 0ₘ = lift₀ 0#
    ; plusₘ = record
      { _∙_ = lift₂ _+_
      ; mono = λ (mk f) (mk g) → mk λ i → +-mono (f i) (g i)
      }
    ; left-scale = record
      { _*ₘ_ = λ r v → lift₁ (r *_) v
      ; *ₘ-mono = λ rr (mk vv) → mk λ i → *-mono rr (vv i)
      }
    ; right-scale = record
      { _ₘ*_ = λ v r → lift₁ (_* r) v
      ; ₘ*-mono = λ (mk vv) rr → mk λ i → *-mono (vv i) rr
      }
    ; isSkewBisemimodule = record
      { isSkewCommutativeMonoid = record
        { isLeftSkewMonoid = record
          { identity = (λ v → mk λ i → +.identity-→ .proj₁ (v i))
                     , (λ v → mk λ i → +.identity-→ .proj₂ (v i))
          ; assoc = λ u v w → mk λ i → +.assoc-→ (u i) (v i) (w i)
          }
        ; isRightSkewMonoid = record
          { identity = (λ v → mk λ i → +.identity-← .proj₁ (v i))
                     , (λ v → mk λ i → +.identity-← .proj₂ (v i))
          ; assoc = λ u v w → mk λ i → +.assoc-← (u i) (v i) (w i)
          }
        ; comm = λ u v → mk λ i → +.comm (u i) (v i)
        }
      ; *ₘ-identityˡ = λ v → mk λ i → *.identity .proj₁ (v i)
      ; *ₘ-assoc = λ r s v → mk λ i → *.assoc r s (v i)
      ; *ₘ-annihil = (λ v → mk λ i → annihil .proj₁ (v i))
                   , (λ r → mk λ i → annihil .proj₂ r)
      ; *ₘ-distrib = (λ r s v → mk λ i → distrib .proj₁ r s (v i))
                   , (λ r u v → mk λ i → distrib .proj₂ r (u i) (v i))
      ; ₘ*-identityʳ = λ v → mk λ i → *.identity .proj₂ (v i)
      ; ₘ*-assoc = λ v r s → mk λ i → *.assoc (v i) r s
      ; ₘ*-annihil = (λ r → mk λ i → annihil .proj₁ r)
                   , (λ v → mk λ i → annihil .proj₂ (v i))
      ; ₘ*-distrib = (λ u v r → mk λ i → distrib .proj₁ (u i) (v i) r)
                   , (λ v r s → mk λ i → distrib .proj₂ (v i) r s)
      ; *ₘ-ₘ*-assoc = λ r v s → mk λ i → *.assoc r (v i) s
      }
    } where open SkewSemiring R

  LinMap : ∀ {cr ℓr cs ℓs}
           {R : SkewSemiring cr ℓr} {S : SkewSemiring cs ℓs}
           (f : SkewSemiringMor R S) (s t : LTree) → Set _
  LinMap {R = R} {S} f s t = SkewBisemimoduleMor
    f f (Vector-skewBisemimodule R s) (Vector-skewBisemimodule S t)
