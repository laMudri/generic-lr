{-# OPTIONS --without-K --safe --postfix-projections #-}

module Algebra.Skew.Construct.Vector where

  open import Algebra.Skew
  open import Data.LTree
  open import Data.LTree.Vector
  -- open import Data.Nat as N using (ℕ)
  -- open import Data.Nat.Properties as NP
  open import Data.Product
  open import Data.Product.Relation.Binary.Pointwise.NonDependent
  open import Data.Unit.Polymorphic
  open import Level using (Level; 0ℓ)
  open import Function.Base
  -- open import Relation.Binary.PropositionalEquality as ≡
  --   using (_≡_; cong; subst)

  infixl 2 _<*>_

  pure : ∀ {a} {A : Set a} → A → A × A
  pure x = x , x

  _<*>_ : ∀ {a b x y} {A : Set a} {B : Set b} {X : A → Set x} {Y : B → Set y} →
          ((a : A) → X a) × ((b : B) → Y b) →
          ((a , b) : A × B) → X a × Y b
  (f , g) <*> (x , y) = f x , g y

  {-
  ℕ-skewSemiring : SkewSemiring 0ℓ 0ℓ
  ℕ-skewSemiring = record
    { proset = record
      { Carrier = ℕ
      ; _≤_ = N._≤_
      ; isProset = record { refl = ≤-refl ; trans = ≤-trans }
      }
    ; 0# = 0
    ; plus = record { _∙_ = N._+_ ; mono = +-mono-≤ }
    ; 1# = 1
    ; mult = record { _∙_ = N._*_ ; mono = *-mono-≤ }
    ; isSkewSemiring = record
      { +-isSkewCommutativeMonoid = record
        { isLeftSkewMonoid = record
          { identity = (λ n → ≤-reflexive (+-identityˡ n))
                     , (λ n → ≤-reflexive (≡.sym (+-identityʳ n)))
          ; assoc = λ m n o → ≤-reflexive (+-assoc m n o)
          }
        ; isRightSkewMonoid = record
          { identity = (λ n → ≤-reflexive (≡.sym (+-identityˡ n)))
                     , (λ n → ≤-reflexive (+-identityʳ n))
          ; assoc = λ m n o → ≤-reflexive (≡.sym (+-assoc m n o))
          }
        ; comm = λ m n → ≤-reflexive (+-comm m n)
        }
      ; *-isSkewMonoid = record
        { identity = (λ n → ≤-reflexive (*-identityˡ n))
                   , (λ n → ≤-reflexive (≡.sym (*-identityʳ n)))
        ; assoc = λ m n o → ≤-reflexive (*-assoc m n o)
        }
      ; annihil = (λ n → ≤-reflexive (*-zeroˡ n))
                , (λ n → ≤-reflexive (≡.sym (*-zeroʳ n)))
      ; distrib = (λ m n o → ≤-reflexive (*-distribʳ-+ o m n))
                , (λ m n o → ≤-reflexive (≡.sym (*-distribˡ-+ m n o)))
      }
    }
  -}

  I-skewLeftSemimodule :
    ∀ {c ℓ} {R : SkewSemiring c ℓ} → SkewLeftSemimodule R c ℓ
  I-skewLeftSemimodule {R = R} = record
    { proset = proset
    ; 0ₘ = 0#
    ; plusₘ = plus
    ; left-scale = record { _*ₘ_ = _*_ ; *ₘ-mono = *-mono }
    ; isSkewLeftSemimodule = record
      { isSkewCommutativeMonoid = +-isSkewCommutativeMonoid
      ; *ₘ-identityˡ = *.identity .proj₁
      ; *ₘ-assoc = *.assoc
      ; *ₘ-annihil = annihil
      ; *ₘ-distrib = distrib
      }
    } where open SkewSemiring R

  Vector-skewLeftSemimodule :
    ∀ {c ℓ} (R : SkewSemiring c ℓ) → LTree →
    SkewLeftSemimodule R c ℓ
  Vector-skewLeftSemimodule R s = record
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
    ; isSkewLeftSemimodule = record
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
      }
    } where open SkewSemiring R

  module _ {cr ℓr cs ℓs cm ℓm cn ℓn}
    {R : SkewSemiring cr ℓr} {S : SkewSemiring cs ℓs}
    {f : SkewSemiringMor R S}
    {M : SkewLeftSemimodule R cm ℓm} {N : SkewLeftSemimodule S cn ℓn}
    where

    open SkewLeftSemimoduleMor
    open ProsetMor
    open SkewSemiringMor

    private
      module M = SkewLeftSemimodule M
      module N = SkewLeftSemimodule N

    -- TODO: this should be factored through the zero object
    0ᴹ : SkewLeftSemimoduleMor f M N
    0ᴹ .prosetMor .apply u = N.0ₘ
    0ᴹ .prosetMor .hom-mono uu = N.refl
    0ᴹ .hom-0ₘ = N.refl
    0ᴹ .hom-+ₘ u v = N.+ₘ-identity-→ .proj₂ N.0ₘ
    0ᴹ .hom-*ₘ r u = N.*ₘ-annihil .proj₂ (f .apply r)

  LinMap : ∀ {cr ℓr cs ℓs}
           {R : SkewSemiring cr ℓr} {S : SkewSemiring cs ℓs}
           (f : SkewSemiringMor R S) (s t : LTree) → Set _
  LinMap {R = R} {S} f s t = SkewLeftSemimoduleMor
    f (Vector-skewLeftSemimodule R s) (Vector-skewLeftSemimodule S t)

  module _ {cr ℓr cs ℓs}
    {R : SkewSemiring cr ℓr} {S : SkewSemiring cs ℓs}
    {f : SkewSemiringMor R S}
    where

    open SkewLeftSemimoduleMor
    open ProsetMor
    open SkewSemiringMor
    open SkewSemiring S

    1ᴹ : ∀ {s} → LinMap f s s
    1ᴹ .prosetMor .apply u i = f .apply (u i)
    1ᴹ .prosetMor .hom-mono uu .get i = f .hom-mono (uu .get i)
    1ᴹ .hom-0ₘ .get i = f .hom-0#
    1ᴹ .hom-+ₘ u v .get i = f .hom-+ (u i) (v i)
    1ᴹ .hom-*ₘ r u .get i = f .hom-* r (u i)

    -- TODO: could do more compositionally, particularly in + case.
    ∑ᴹ : ∀ {s} → SkewLeftSemimoduleMor f (Vector-skewLeftSemimodule R s)
                                         I-skewLeftSemimodule
    ∑ᴹ {[-]} .prosetMor .apply v = f .apply (v here)
    ∑ᴹ {[-]} .prosetMor .hom-mono (mk vv) = f .hom-mono (vv here)
    ∑ᴹ {[-]} .hom-0ₘ = f .hom-0#
    ∑ᴹ {[-]} .hom-+ₘ u v = f .hom-+ (u here) (v here)
    ∑ᴹ {[-]} .hom-*ₘ r v = f .hom-* r (v here)
    ∑ᴹ {ε} = 0ᴹ
    ∑ᴹ {s <+> t} .prosetMor .apply v = ∑ᴹ .apply (v ∘ ↙) + ∑ᴹ .apply (v ∘ ↘)
    ∑ᴹ {s <+> t} .prosetMor .hom-mono (mk vv) =
      +-mono (∑ᴹ .hom-mono (mk (vv ∘ ↙))) (∑ᴹ .hom-mono (mk (vv ∘ ↘)))
    ∑ᴹ {s <+> t} .hom-0ₘ = trans (+-mono (∑ᴹ {s} .hom-0ₘ) (∑ᴹ {t} .hom-0ₘ))
                                 (+.identity-→ .proj₁ 0#)
    ∑ᴹ {s <+> t} .hom-+ₘ u v =
      trans (+-mono (∑ᴹ {s} .hom-+ₘ _ _) (∑ᴹ {t} .hom-+ₘ _ _))
            (+.inter _ _ _ _)
    ∑ᴹ {s <+> t} .hom-*ₘ r v =
      trans (+-mono (∑ᴹ {s} .hom-*ₘ _ _) (∑ᴹ {t} .hom-*ₘ _ _))
            (distrib .proj₂ _ _ _)

  -- module _ where
  -- ∑ : ∀ {s} → Vector Carrier s → Carrier

  module _ {cr ℓr cs ℓs} {R : SkewSemiring cr ℓr} {S : SkewSemiring cs ℓs}
           {f : SkewSemiringMor R S} where
    open SkewLeftSemimoduleMor
    open ProsetMor

    private
      module R = SkewSemiring R
      module S = SkewSemiring S
      variable
        s s′ t t′ : LTree

    [_─_] : LinMap f s t → LinMap f s′ t → LinMap f (s <+> s′) t
    [ M ─ N ] .prosetMor .apply u j =
      M .apply (u ∘ ↙) j S.+ N .apply (u ∘ ↘) j
    [ M ─ N ] .prosetMor .hom-mono (mk uu) .get j =
      S.+-mono (M .hom-mono (mk (uu ∘ ↙)) .get j)
               (N .hom-mono (mk (uu ∘ ↘)) .get j)
    [ M ─ N ] .hom-0ₘ .get j =
      S.trans (S.+-mono (M .hom-0ₘ .get j) (N .hom-0ₘ .get j))
              (S.+.identity-→ .proj₁ _)
    [ M ─ N ] .hom-+ₘ u v .get j =
      S.trans (S.+-mono (M .hom-+ₘ (u ∘ ↙) (v ∘ ↙) .get j)
                        (N .hom-+ₘ (u ∘ ↘) (v ∘ ↘) .get j))
              (S.+.inter _ _ _ _)
    [ M ─ N ] .hom-*ₘ r u .get j =
      S.trans (S.+-mono (M .hom-*ₘ r (u ∘ ↙) .get j)
                        (N .hom-*ₘ r (u ∘ ↘) .get j))
              (S.distrib .proj₂ _ _ _)

    [_│_] : LinMap f s t → LinMap f s t′ → LinMap f s (t <+> t′)
    [ M │ N ] .prosetMor .apply u = M .apply u ++ N .apply u
    [ M │ N ] .prosetMor .hom-mono uu = M .hom-mono uu ++₂ N .hom-mono uu
    [ M │ N ] .hom-0ₘ = M .hom-0ₘ ++₂ N .hom-0ₘ
    [ M │ N ] .hom-+ₘ u v = M .hom-+ₘ u v ++₂ N .hom-+ₘ u v
    [ M │ N ] .hom-*ₘ r u = M .hom-*ₘ r u ++₂ N .hom-*ₘ r u

  module _ where
    open ProsetMor

    id-ProsetMor : ∀ {c ℓ P} → ProsetMor {c} {ℓ} P P
    id-ProsetMor .apply = id
    id-ProsetMor .hom-mono = id

    >>-ProsetMor : ∀ {p pℓ q qℓ r rℓ P Q R} →
                   ProsetMor P Q → ProsetMor {q} {qℓ} Q R →
                   ProsetMor {p} {pℓ} {r} {rℓ} P R
    >>-ProsetMor f g .apply = g .apply ∘ f .apply
    >>-ProsetMor f g .hom-mono = g .hom-mono ∘ f .hom-mono

  module _ {c ℓ} {R : SkewSemiring c ℓ} where

    module _ where
      open SkewSemiringMor
      open SkewSemiring R

      id-SkewSemiringMor : SkewSemiringMor R R
      id-SkewSemiringMor .prosetMor = id-ProsetMor
      id-SkewSemiringMor .hom-0# = refl
      id-SkewSemiringMor .hom-+ _ _ = refl
      id-SkewSemiringMor .hom-1# = refl
      id-SkewSemiringMor .hom-* _ _ = refl

    module _ {m mℓ} {M : SkewLeftSemimodule R m mℓ} where
      open SkewLeftSemimoduleMor
      open SkewLeftSemimodule M

      ──-SkewLeftSemimoduleMor :
        SkewLeftSemimoduleMor id-SkewSemiringMor M M
      ──-SkewLeftSemimoduleMor .prosetMor = id-ProsetMor
      ──-SkewLeftSemimoduleMor .hom-0ₘ = refl
      ──-SkewLeftSemimoduleMor .hom-+ₘ _ _ = refl
      ──-SkewLeftSemimoduleMor .hom-*ₘ _ _ = refl

  module _ {r rℓ s sℓ t tℓ} {R : SkewSemiring r rℓ}
           {S : SkewSemiring s sℓ} {T : SkewSemiring t tℓ} where

    open SkewSemiringMor

    module _ where
      open SkewSemiring T

      >>-SkewSemiringMor : SkewSemiringMor R S → SkewSemiringMor S T →
                           SkewSemiringMor R T
      >>-SkewSemiringMor f g .prosetMor =
        >>-ProsetMor (f .prosetMor) (g .prosetMor)
      >>-SkewSemiringMor f g .hom-0# =
        trans (g .hom-mono (f .hom-0#)) (g .hom-0#)
      >>-SkewSemiringMor f g .hom-+ _ _ =
        trans (g .hom-mono (f .hom-+ _ _)) (g .hom-+ _ _)
      >>-SkewSemiringMor f g .hom-1# =
        trans (g .hom-mono (f .hom-1#)) (g .hom-1#)
      >>-SkewSemiringMor f g .hom-* _ _ =
        trans (g .hom-mono (f .hom-* _ _)) (g .hom-* _ _)

    module _
      {f : SkewSemiringMor R S} {g : SkewSemiringMor S T} {m mℓ n nℓ o oℓ}
      {M : SkewLeftSemimodule R m mℓ} {N : SkewLeftSemimodule S n nℓ}
      {O : SkewLeftSemimodule T o oℓ} where

      open SkewLeftSemimoduleMor
      open SkewLeftSemimodule O

      vv-SkewLeftSemimoduleMor :
        SkewLeftSemimoduleMor f M N → SkewLeftSemimoduleMor g N O →
        SkewLeftSemimoduleMor (>>-SkewSemiringMor f g) M O
      vv-SkewLeftSemimoduleMor F G .prosetMor =
        >>-ProsetMor (F .prosetMor) (G .prosetMor)
      vv-SkewLeftSemimoduleMor F G .hom-0ₘ =
        trans (G .hom-mono (F .hom-0ₘ)) (G .hom-0ₘ)
      vv-SkewLeftSemimoduleMor F G .hom-+ₘ _ _ =
        trans (G .hom-mono (F .hom-+ₘ _ _)) (G .hom-+ₘ _ _)
      vv-SkewLeftSemimoduleMor F G .hom-*ₘ _ _ =
        trans (G .hom-mono (F .hom-*ₘ _ _)) (G .hom-*ₘ _ _)
