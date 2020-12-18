{-# OPTIONS --safe --without-K #-}

open import Algebra.Skew
open import Level renaming (zero to lzero; suc to lsuc)

module Generic.Linear.Syntax.Interpretation.Map
  (Ty : Set) (skewSemiring : SkewSemiring lzero lzero)
  where

  open import Algebra.Skew.Relation
  open import Algebra.Skew.Construct.Vector hiding (pure; _<*>_)
  open import Data.Unit.Polymorphic
  open import Data.Product
  open import Data.LTree
  open import Data.LTree.Vector
  open import Function.Base
  open import Relation.Binary.PropositionalEquality as ≡
  open import Relation.Unary
  open import Relation.Unary.Bunched

  open SkewSemiring skewSemiring renaming (Carrier to Ann)

  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Algebra skewSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawSkewSemiring

  private
    variable
      x y : Level
      fl : PremisesFlags

  LinRel : ∀ {c ℓ} (R : SkewSemiring c ℓ) (s t : LTree) → Set _
  LinRel R s t = SkewLeftSemimoduleRel
    (Vector-skewLeftSemimodule R s) (Vector-skewLeftSemimodule R t) 0ℓ

  LinMor : ∀ {c ℓ} (R : SkewSemiring c ℓ) (s t : LTree) → Set _
  LinMor R s t = SkewLeftSemimoduleMor id-SkewSemiringMor
    (Vector-skewLeftSemimodule R s) (Vector-skewLeftSemimodule R t)

  module _ {s t} {Γ : Vector Ty s} {Δ : Vector Ty t}
           (F : LinMor skewSemiring s t)
           {X : Ctx → Scoped x} {Y : Ctx → Scoped y}
    where

    open SkewLeftSemimoduleMor F

    map-p : (ps : Premises fl) →
      (∀ {RΘ A P Q} → Q ⊴* apply P → X RΘ A (ctx P Γ) → Y RΘ A (ctx Q Δ)) →
      (∀ {P Q} → Q ⊴* apply P → ⟦ ps ⟧p X (ctx P Γ) → ⟦ ps ⟧p Y (ctx Q Δ))
    map-p (⟨ PΓ `⊢ A ⟩) f r t = f r t
    map-p `⊤ f r tt = tt
    map-p `ℑ f r ℑ⟨ t ⟩ =
      ℑ⟨ (⊴*-trans r (⊴*-trans (hom-mono t) hom-0ₘ)) ⟩
    map-p (ps `∧ qs) f r (s , t) = map-p ps f r s , map-p qs f r t
    map-p (ps `✴ qs) f r (s ✴⟨ sp ⟩ t) =
      let sp′ = ⊴*-trans r (⊴*-trans (hom-mono sp) (hom-+ₘ _ _)) in
      map-p ps f ⊴*-refl s ✴⟨ sp′ ⟩ map-p qs f ⊴*-refl t
    map-p (ρ `· ps) f r (⟨ sp ⟩· t) =
      let sp′ = ⊴*-trans r (⊴*-trans (hom-mono sp) (hom-*ₘ _ _)) in
      ⟨ sp′ ⟩· map-p ps f ⊴*-refl t
    map-p (`□ ps) f r (□⟨ str , sp0 , sp+ ⟩ t) =
      □⟨ ⊴*-trans r (hom-mono str)
       , ⊴*-trans (hom-mono sp0) hom-0ₘ
       , ⊴*-trans (hom-mono sp+) (hom-+ₘ _ _)
       ⟩ map-p ps f ⊴*-refl t

    map-r : (r : Rule fl) →
      (∀ {RΘ A P Q} → Q ⊴* apply P → X RΘ A (ctx P Γ) → Y RΘ A (ctx Q Δ)) →
      (∀ {A P Q} → Q ⊴* apply P → ⟦ r ⟧r X A (ctx P Γ) → ⟦ r ⟧r Y A (ctx Q Δ))
    map-r (ps =⇒ A) f r (q , t) = q , map-p ps f r t

    map-s : (s : System fl) →
       (∀ {RΘ A P Q} → Q ⊴* apply P → X RΘ A (ctx P Γ) → Y RΘ A (ctx Q Δ)) →
       (∀ {A P Q} → Q ⊴* apply P → ⟦ s ⟧s X A (ctx P Γ) → ⟦ s ⟧s Y A (ctx Q Δ))
    map-s (L ▹ rs) f r (l , t) = l , map-r (rs l) f r t

  -- map-s′ : ∀ {X : Ctx → Scoped x} {Y : Ctx → Scoped y} (s : System fl) →
  --   (∀ {RΘ A u Γ P Q} → Q ⊴* P → X RΘ A (ctx P Γ) → Y RΘ A (ctx {u} Q Γ)) →
  --   (∀ {A} → ∀[ ⟦ s ⟧s X A ⇒ ⟦ s ⟧s Y A ])
  -- map-s′ s f t = map-s ──-SkewLeftSemimoduleMor s f ⊴*-refl t

  module _ {X : Ctx → Scoped x} {Y : Ctx → Scoped y} where

    map-p′ : (ps : Premises fl) → (∀ {RΘ A} → ∀[ X RΘ A ⇒ Y RΘ A ]) →
             ∀[ ⟦ ps ⟧p X ⇒ ⟦ ps ⟧p Y ]
    map-p′ ⟨ PΓ `⊢ A ⟩ f t = f t
    map-p′ `⊤ f tt = tt
    map-p′ `ℑ f ℑ⟨ sp ⟩ = ℑ⟨ sp ⟩
    map-p′ (ps `∧ qs) f (s , t) = map-p′ ps f s , map-p′ qs f t
    map-p′ (ps `✴ qs) f (s ✴⟨ sp ⟩ t) =
      map-p′ ps f s ✴⟨ sp ⟩ map-p′ qs f t
    map-p′ (r `· ps) f (⟨ sp ⟩· t) = ⟨ sp ⟩· map-p′ ps f t
    map-p′ (`□ ps) f (□⟨ str , sp0 , sp+ ⟩ t) =
      □⟨ str , sp0 , sp+ ⟩ map-p′ ps f t

    map-r′ : (r : Rule fl) → (∀ {RΘ A} → ∀[ X RΘ A ⇒ Y RΘ A ]) →
             (∀ {A} → ∀[ ⟦ r ⟧r X A ⇒ ⟦ r ⟧r Y A ])
    map-r′ (ps =⇒ A) f (q , t) = q , map-p′ ps f t

    map-s′ : (s : System fl) → (∀ {RΘ A} → ∀[ X RΘ A ⇒ Y RΘ A ]) →
             (∀ {A} → ∀[ ⟦ s ⟧s X A ⇒ ⟦ s ⟧s Y A ])
    map-s′ (L ▹ rs) f (l , t) = l , map-r′ (rs l) f t

  open import Category.Applicative

  module _ {F : Set x → Set x} {{appF : RawApplicative F}} where

    open RawApplicative appF

    sequence-p :
      ∀ {X : Ctx → Scoped x} (ps : Premises fl) →
      ∀[ ⟦ ps ⟧p (λ QΔ B PΓ → F (X QΔ B PΓ)) ⇒ F ∘ ⟦ ps ⟧p X ]
    sequence-p (⟨ PΓ `⊢ A ⟩) t = t
    sequence-p `⊤ tt = pure tt
    sequence-p `ℑ t = pure t
    sequence-p (ps `∧ qs) (s , t) = _,_ <$> sequence-p ps s ⊛ sequence-p qs t
    sequence-p (ps `✴ qs) (s ✴⟨ sp ⟩ t) =
      _✴⟨ sp ⟩_ <$> sequence-p ps s ⊛ sequence-p qs t
    sequence-p (ρ `· ps) (⟨ sp ⟩· t) =
      ⟨ sp ⟩·_ <$> sequence-p ps t
    sequence-p (`□ ps) (□⟨ str , sp0 , sp+ ⟩ t) =
      □⟨ str , sp0 , sp+ ⟩_ <$> sequence-p ps t

    sequence-r :
      ∀ {X : Ctx → Scoped x} (r : Rule fl) →
      ∀ {A} → ∀[ ⟦ r ⟧r (λ QΔ B PΓ → F (X QΔ B PΓ)) A ⇒ F ∘ ⟦ r ⟧r X A ]
    sequence-r (ps =⇒ A) (q , t) = (q ,_) <$> sequence-p ps t

    sequence-s :
      ∀ {X : Ctx → Scoped x} (s : System fl) →
      ∀ {A} → ∀[ ⟦ s ⟧s (λ QΔ B PΓ → F (X QΔ B PΓ)) A ⇒ F ∘ ⟦ s ⟧s X A ]
    sequence-s (L ▹ rs) (l , t) =
      (l ,_) <$> sequence-r (rs l) t
