{-# OPTIONS --without-K --safe --postfix-projections #-}

module Algebra.Po.Construct.Vector where

  open import Algebra.Po
  open import Data.LTree
  open import Data.LTree.Vector as V hiding (setoid)
  -- open import Data.Nat as N using (ℕ)
  -- open import Data.Nat.Properties as NP
  open import Data.Product hiding (_<*>_)
  open import Data.Product.Relation.Binary.Pointwise.NonDependent
  open import Data.Unit.Polymorphic
  open import Level using (Level; 0ℓ)
  open import Function.Base
  open import Relation.Binary using (Setoid)
  -- open import Relation.Binary.PropositionalEquality as ≡
  --   using (_≡_; cong; subst)

  private
    infixl 2 _<*>_

    pure : ∀ {a} {A : Set a} → A → A × A
    pure x = x , x

    _<*>_ : ∀ {a b x y} {A : Set a} {B : Set b} {X : A → Set x} {Y : B → Set y} →
            ((a : A) → X a) × ((b : B) → Y b) →
            ((a , b) : A × B) → X a × Y b
    (f , g) <*> (x , y) = f x , g y

    _>>_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (f : (x : A) → B x) (g : {x : A} (y : B x) → C y) → ((x : A) → C (f x))
    _>>_ = flip _∘_

  I-poLeftSemimodule :
    ∀ {c ℓ₁ ℓ₂} {R : PoSemiring c ℓ₁ ℓ₂} → PoLeftSemimodule R c ℓ₁ ℓ₂
  I-poLeftSemimodule {R = R} = record
    { Carrierₘ = Carrier
    ; _≈ₘ_ = _≈_
    ; _≤ₘ_ = _≤_
    ; 0ₘ = 0#
    ; _+ₘ_ = _+_
    ; _*ₘ_ = _*_
    ; isPoLeftSemimodule = record
      { +ₘ-isPoCommutativeMonoid = +-isPoCommutativeMonoid
      ; *ₘ-identity = *-identityˡ
      ; *ₘ-assoc = *-assoc
      ; *ₘ-annihilˡ = annihilˡ
      ; *ₘ-annihilʳ = annihilʳ
      ; *ₘ-distribˡ = distribˡ
      ; *ₘ-distribʳ = distribʳ
      }
    } where open PoSemiring R

  Vector-poLeftSemimodule :
    ∀ {c ℓ₁ ℓ₂} (R : PoSemiring c ℓ₁ ℓ₂) → LTree →
    PoLeftSemimodule R c ℓ₁ ℓ₂
  Vector-poLeftSemimodule R s = record
    { Carrierₘ = Vector Carrier s
    ; _≈ₘ_ = Lift₂ _≈_
    ; _≤ₘ_ = Lift₂ _≤_
    ; 0ₘ = lift₀ 0#
    ; _+ₘ_ = lift₂ _+_
    ; _*ₘ_ = λ r v → lift₁ (r *_) v
    ; isPoLeftSemimodule = record
      { +ₘ-isPoCommutativeMonoid = record
        { isPoMonoid = record
          { isPartialOrder = record
            { isPreorder = record
              { isEquivalence = isEquivalenceV
              ; reflexive = λ { q .get i → ≤-reflexive (q .get i) }
              ; trans = λ { xy yz .get i → ≤-trans (xy .get i) (yz .get i) }
              }
            ; antisym = λ { xy yx .get i → antisym (xy .get i) (yx .get i) }
            }
          ; isMonoid = record
            { isSemigroup = record
              { isMagma = record
                { isEquivalence = isEquivalenceV
                ; ∙-cong = λ { xx yy .get i → +-cong (xx .get i) (yy .get i) }
                }
              ; assoc = λ { x y z .get i → +-assoc (x i) (y i) (z i) }
              }
            ; identity = λ where
              .proj₁ x .get i → +-identityˡ (x i)
              .proj₂ x .get i → +-identityʳ (x i)
            }
          ; ∙-monoˡ = λ { xx .get i → +-monoˡ (xx .get i) }
          ; ∙-monoʳ = λ { xx .get i → +-monoʳ (xx .get i) }
          }
        ; comm = λ { x y .get i → +-comm (x i) (y i) }
        }
      ; *ₘ-identity = λ { v .get i → *-identityˡ (v i) }
      ; *ₘ-assoc = λ { r s v .get i → *-assoc r s (v i) }
      ; *ₘ-annihilˡ = λ { v .get i → annihilˡ (v i) }
      ; *ₘ-annihilʳ = λ { r .get i → annihilʳ r }
      ; *ₘ-distribˡ = λ { v r s .get i → distribˡ (v i) r s }
      ; *ₘ-distribʳ = λ { r v w .get i → distribʳ r (v i) (w i) }
      }
    }
    where
    open PoSemiring R
    isEquivalenceV = Setoid.isEquivalence (V.setoid setoid s)

  module _ {cr ℓr₁ ℓr₂ cs ℓs₁ ℓs₂ cm ℓm₁ ℓm₂ cn ℓn₁ ℓn₂}
    {R : PoSemiring cr ℓr₁ ℓr₂} {S : PoSemiring cs ℓs₁ ℓs₂}
    {f : PoSemiringMor R S}
    {M : PoLeftSemimodule R cm ℓm₁ ℓm₂} {N : PoLeftSemimodule S cn ℓn₁ ℓn₂}
    where

    open PoLeftSemimoduleMor
    open PoSemiringMor

    private
      module M = PoLeftSemimodule M
      module N = PoLeftSemimodule N

    -- TODO: this should be factored through the zero object
    0ᴹ : PoLeftSemimoduleMor f M N
    0ᴹ .hom u = N.0ₘ
    0ᴹ .hom-cong uu = N.refl
    0ᴹ .hom-mono uu = N.≤-refl
    0ᴹ .hom-0ₘ = N.refl
    0ᴹ .hom-+ₘ u v = N.sym (N.+ₘ-identityʳ N.0ₘ)
    0ᴹ .hom-*ₘ r u = N.sym (N.*ₘ-annihilʳ _)

  LinMap : ∀ {cr ℓr₁ ℓr₂ cs ℓs₁ ℓs₂}
           {R : PoSemiring cr ℓr₁ ℓr₂} {S : PoSemiring cs ℓs₁ ℓs₂}
           (f : PoSemiringMor R S) (s t : LTree) → Set _
  LinMap {R = R} {S} f s t = PoLeftSemimoduleMor
    f (Vector-poLeftSemimodule R s) (Vector-poLeftSemimodule S t)

  module _ {cr ℓr₁ ℓr₂ cs ℓs₁ ℓs₂}
    {R : PoSemiring cr ℓr₁ ℓr₂} {S : PoSemiring cs ℓs₁ ℓs₂}
    {f : PoSemiringMor R S}
    where

    open PoLeftSemimoduleMor
    open PoSemiringMor
    open PoSemiring S

    1ᴹ : ∀ {s} → LinMap f s s
    1ᴹ .hom u i = f .hom (u i)
    1ᴹ .hom-cong uu .get i = f .hom-cong (uu .get i)
    1ᴹ .hom-mono uu .get i = f .hom-mono (uu .get i)
    1ᴹ .hom-0ₘ .get i = f .hom-0#
    1ᴹ .hom-+ₘ u v .get i = f .hom-+ (u i) (v i)
    1ᴹ .hom-*ₘ r u .get i = f .hom-* r (u i)

    -- TODO: could do more compositionally, particularly in + case.
    ∑ᴹ : ∀ {s} → PoLeftSemimoduleMor f (Vector-poLeftSemimodule R s)
                                         I-poLeftSemimodule
    ∑ᴹ {[-]} .hom u =  f .hom (u here)
    ∑ᴹ {[-]} .hom-cong uu = f .hom-cong (uu .get here)
    ∑ᴹ {[-]} .hom-mono uu = f .hom-mono (uu .get here)
    ∑ᴹ {[-]} .hom-0ₘ = f .hom-0#
    ∑ᴹ {[-]} .hom-+ₘ u v = f .hom-+ (u here) (v here)
    ∑ᴹ {[-]} .hom-*ₘ r u = f .hom-* r (u here)
    ∑ᴹ {ε} = 0ᴹ
    ∑ᴹ {s <+> t} .hom u = ∑ᴹ .hom (u ∘ ↙) + ∑ᴹ .hom (u ∘ ↘)
    ∑ᴹ {s <+> t} .hom-cong (mk uu) =
      +-cong (∑ᴹ .hom-cong (mk (uu ∘ ↙))) (∑ᴹ .hom-cong (mk (uu ∘ ↘)))
    ∑ᴹ {s <+> t} .hom-mono (mk uu) =
      +-mono (∑ᴹ .hom-mono (mk (uu ∘ ↙))) (∑ᴹ .hom-mono (mk (uu ∘ ↘)))
    ∑ᴹ {s <+> t} .hom-0ₘ = trans
      (+-cong (∑ᴹ {s} .hom-0ₘ) (∑ᴹ {t} .hom-0ₘ))
      (+-identityˡ 0#)
    ∑ᴹ {s <+> t} .hom-+ₘ u v = trans
      (+-cong (∑ᴹ {s} .hom-+ₘ _ _) (∑ᴹ {t} .hom-+ₘ _ _))
      (+-inter _ _ _ _)
    ∑ᴹ {s <+> t} .hom-*ₘ r u = trans
      (+-cong (∑ᴹ {s} .hom-*ₘ _ _) (∑ᴹ {t} .hom-*ₘ _ _))
      (sym (distribʳ _ _ _))

  -- module _ where
  -- ∑ : ∀ {s} → Vector Carrier s → Carrier

  module _ {cr ℓr₁ ℓr₂ cs ℓs₁ ℓs₂}
    {R : PoSemiring cr ℓr₁ ℓr₂} {S : PoSemiring cs ℓs₁ ℓs₂}
    {f : PoSemiringMor R S} where
    open PoLeftSemimoduleMor

    private
      module R = PoSemiring R
      module S = PoSemiring S
      variable
        s s′ t t′ : LTree

    [_─_] : LinMap f s t → LinMap f s′ t → LinMap f (s <+> s′) t
    [ M ─ N ] .hom u j = M .hom (u ∘ ↙) j S.+ N .hom (u ∘ ↘) j
    [ M ─ N ] .hom-cong (mk uu) .get j = S.+-cong
      (M .hom-cong (mk (uu ∘ ↙)) .get j)
      (N .hom-cong (mk (uu ∘ ↘)) .get j)
    [ M ─ N ] .hom-mono (mk uu) .get j = S.+-mono
      (M .hom-mono (mk (uu ∘ ↙)) .get j)
      (N .hom-mono (mk (uu ∘ ↘)) .get j)
    [ M ─ N ] .hom-0ₘ .get j = S.trans
      (S.+-cong (M .hom-0ₘ .get j) (N .hom-0ₘ .get j))
      (S.+-identityˡ S.0#)
    [ M ─ N ] .hom-+ₘ u v .get j = S.trans
      (S.+-cong (M .hom-+ₘ _ _ .get j) (N .hom-+ₘ _ _ .get j))
      (S.+-inter _ _ _ _)
    [ M ─ N ] .hom-*ₘ r u .get j = S.trans
      (S.+-cong (M .hom-*ₘ _ _ .get j) (N .hom-*ₘ _ _ .get j))
      (S.sym (S.distribʳ _ _ _))

    [_│_] : LinMap f s t → LinMap f s t′ → LinMap f s (t <+> t′)
    [ M │ N ] .hom u = M .hom u ++ N .hom u
    [ M │ N ] .hom-cong uu = M .hom-cong uu ++₂ N .hom-cong uu
    [ M │ N ] .hom-mono uu = M .hom-mono uu ++₂ N .hom-mono uu
    [ M │ N ] .hom-0ₘ = M .hom-0ₘ ++₂ N .hom-0ₘ
    [ M │ N ] .hom-+ₘ u v = M .hom-+ₘ u v ++₂ N .hom-+ₘ u v
    [ M │ N ] .hom-*ₘ r u = M .hom-*ₘ r u ++₂ N .hom-*ₘ r u

  {-
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
  -}

  module _ {c ℓ₁ ℓ₂} {R : PoSemiring c ℓ₁ ℓ₂} where

    module _ where
      open PoSemiringMor
      open PoSemiring R

      id-PoSemiringMor : PoSemiringMor R R
      id-PoSemiringMor .hom = id
      id-PoSemiringMor .hom-cong = id
      id-PoSemiringMor .hom-mono = id
      id-PoSemiringMor .hom-0# = refl
      id-PoSemiringMor .hom-+ _ _ = refl
      id-PoSemiringMor .hom-1# = refl
      id-PoSemiringMor .hom-* _ _ = refl

    module _ {m mℓ₁ mℓ₂} {M : PoLeftSemimodule R m mℓ₁ mℓ₂} where
      open PoLeftSemimoduleMor
      open PoLeftSemimodule M

      ──-PoLeftSemimoduleMor : PoLeftSemimoduleMor id-PoSemiringMor M M
      ──-PoLeftSemimoduleMor .hom = id
      ──-PoLeftSemimoduleMor .hom-cong = id
      ──-PoLeftSemimoduleMor .hom-mono = id
      ──-PoLeftSemimoduleMor .hom-0ₘ = refl
      ──-PoLeftSemimoduleMor .hom-+ₘ _ _ = refl
      ──-PoLeftSemimoduleMor .hom-*ₘ _ _ = refl

  module _ {r rℓ₁ rℓ₂ s sℓ₁ sℓ₂ t tℓ₁ tℓ₂} {R : PoSemiring r rℓ₁ rℓ₂}
           {S : PoSemiring s sℓ₁ sℓ₂} {T : PoSemiring t tℓ₁ tℓ₂} where

    open PoSemiringMor

    module _ where
      open PoSemiring T

      >>-PoSemiringMor : PoSemiringMor R S → PoSemiringMor S T →
                           PoSemiringMor R T
      >>-PoSemiringMor f g .hom = f .hom >> g .hom
      >>-PoSemiringMor f g .hom-cong = f .hom-cong >> g .hom-cong
      >>-PoSemiringMor f g .hom-mono = f .hom-mono >> g .hom-mono
      >>-PoSemiringMor f g .hom-0# = trans (g .hom-cong (f .hom-0#)) (g .hom-0#)
      >>-PoSemiringMor f g .hom-+ _ _ =
        trans (g .hom-cong (f .hom-+ _ _)) (g .hom-+ _ _)
      >>-PoSemiringMor f g .hom-1# = trans (g .hom-cong (f .hom-1#)) (g .hom-1#)
      >>-PoSemiringMor f g .hom-* _ _ =
        trans (g .hom-cong (f .hom-* _ _)) (g .hom-* _ _)

    module _
      {f : PoSemiringMor R S} {g : PoSemiringMor S T}
      {m mℓ₁ mℓ₂ n nℓ₁ nℓ₂ o oℓ₁ oℓ₂} {M : PoLeftSemimodule R m mℓ₁ mℓ₂}
      {N : PoLeftSemimodule S n nℓ₁ nℓ₂} {O : PoLeftSemimodule T o oℓ₁ oℓ₂}
      where

      open PoLeftSemimoduleMor
      open PoLeftSemimodule O

      vv-PoLeftSemimoduleMor :
        PoLeftSemimoduleMor f M N → PoLeftSemimoduleMor g N O →
        PoLeftSemimoduleMor (>>-PoSemiringMor f g) M O
      vv-PoLeftSemimoduleMor F G .hom = F .hom >> G .hom
      vv-PoLeftSemimoduleMor F G .hom-cong = F .hom-cong >> G .hom-cong
      vv-PoLeftSemimoduleMor F G .hom-mono = F .hom-mono >> G .hom-mono
      vv-PoLeftSemimoduleMor F G .hom-0ₘ =
        trans (G .hom-cong (F .hom-0ₘ)) (G .hom-0ₘ)
      vv-PoLeftSemimoduleMor F G .hom-+ₘ _ _ =
        trans (G .hom-cong (F .hom-+ₘ _ _)) (G .hom-+ₘ _ _)
      vv-PoLeftSemimoduleMor F G .hom-*ₘ _ _ =
        trans (G .hom-cong (F .hom-*ₘ _ _)) (G .hom-*ₘ _ _)
