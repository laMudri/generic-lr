{-# OPTIONS --safe --without-K --prop #-}

open import Algebra.Po
open import Level using (Level; 0ℓ)

module Generic.Linear.Syntax.Interpretation.Map
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open import Algebra.Po.Relation
  open import Algebra.Po.Construct.Vector
  open import Algebra.Relational
  open import Algebra.Relational.Relation
  open import Data.Unit.Polymorphic
  open import Data.Product
  open import Data.LTree
  open import Data.LTree.Vector
  open import Function.Base
  open import Function.Extra
  open import Relation.Binary.PropositionalEquality as ≡
  open import Relation.Nary
  open import Relation.Unary.Bunched

  open PoSemiring poSemiring renaming (Carrier to Ann)

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring

  private
    variable
      x y : Level
      fl : PremisesFlags

  {-
  module _ {ℓ s t} {γ : Vector Ty s} {δ : Vector Ty t}
           (F : LinRel s t ℓ)
           {X : Ctx → Scoped x} {Y : Ctx → Scoped y}
    where

    -- open RelLeftSemimoduleRel F

    map-pᴿ : (ps : Premises fl) →
      (∀ {Θ A P Q} → F .rel P Q → X Θ A (ctx P γ) → Y Θ A (ctx Q δ)) →
      (∀ {P Q} → F .rel P Q → ⟦ ps ⟧p X (ctx P γ) → ⟦ ps ⟧p Y (ctx Q δ))
    map-pᴿ ⟨ Γ `⊢ A ⟩ f r t = {!!}
    map-pᴿ `⊤ f r t = {!!}
    map-pᴿ (ps `∧ qs) f r t = {!!}
    map-pᴿ `ℑ f r t = {!!}
    map-pᴿ (ps `✴ qs) f r t = {!!}
    map-pᴿ (p `· ps) f r t = {!!}
    map-pᴿ (`□ ps) f r (□⟨ str , sp0 , sp+ ⟩ t) =
      let r′ , str′ = F .rel-comm-≤ₘ (str , r) in
      □⟨ str′ , {!sp0!} , {!!} ⟩ map-pᴿ ps f r′ t

    map-sᴿ : (s : System fl) →
      (∀ {Θ A P Q} → F .rel P Q → X Θ A (ctx P γ) → Y Θ A (ctx Q δ)) →
      (∀ {A P Q} → F .rel P Q → ⟦ s ⟧s X A (ctx P γ) → ⟦ s ⟧s Y A (ctx Q δ))
    map-sᴿ s f r t = {!!}
  -}

  module _ {s t} {γ : Vector Ty s} {δ : Vector Ty t}
    (F : LinMor s t) {X : ExtOpenFam x} {Y : ExtOpenFam y}
    where

    -- open PoLeftSemimoduleMor F
    private open module Dummy {s} = FRelLeftSemimodule (Vᶠᴿ s)

    map-p : (ps : Premises fl) →
      (∀ {Θ P Q} → Q ≤* F .hom P → ∀[ X Θ (ctx P γ) ⇒ Y Θ (ctx Q δ) ]) →
      (∀ {P Q} → Q ≤* F .hom P → ⟦ ps ⟧p X (ctx P γ) → ⟦ ps ⟧p Y (ctx Q δ))
    map-p (⟨ Γ `⊢ A ⟩) f r t = f r t
    map-p `⊤ f r _ = _
    map-p (ps `∧ qs) f r (s , t) = map-p ps f r s , map-p qs f r t
    map-p `ℑ f r ℑ⟨ t ⟩ =
      ℑ⟨ 0ₘ-mono (≤*-trans r (F .hom-mono (0*→≤* t))) (≈*→0* (F .hom-0ₘ)) ⟩
    map-p (ps `✴ qs) f r (s ✴⟨ sp ⟩ t) =
      let sp′ = +ₘ-mono (≤*-trans r (F .hom-mono (+*→≤* sp))) ≤*-refl ≤*-refl
           (≈*→+* (F .hom-+ₘ _ _))
      in map-p ps f ≤*-refl s ✴⟨ sp′ ⟩ map-p qs f ≤*-refl t
    map-p (p `· ps) f r (⟨ sp ⟩· t) =
      let sp′ = *ₘ-mono (≤*-trans r (F .hom-mono (*ₗ→≤* sp))) ≤-refl ≤*-refl
           (≈*→*ₗ (F .hom-*ₘ _ _))
      in ⟨ sp′ ⟩· map-p ps f ≤*-refl t
    map-p (`□ ps) f r (□⟨ str , sp0 , sp+ ⟩ t) =
      □⟨ ≤*-trans r (F .hom-mono str)
       , ≤*-trans (F .hom-mono sp0) (≤*-reflexive (F .hom-0ₘ))
       , ≤*-trans (F .hom-mono sp+) (≤*-reflexive (F .hom-+ₘ _ _))
       ⟩ map-p ps f ≤*-refl t

    map-r : (r : Rule fl) →
      (∀ {Θ P Q} → Q ≤* F .hom P → ∀[ X Θ (ctx P γ) ⇒ Y Θ (ctx Q δ) ]) →
      (∀ {P Q} → Q ≤* F .hom P → ∀[ ⟦ r ⟧r X (ctx P γ) ⇒ ⟦ r ⟧r Y (ctx Q δ) ])
    map-r (ps =⇒ A) f r (q , t) = q , map-p ps f r t

    map-s : (s : System fl) →
      (∀ {Θ P Q} → Q ≤* F .hom P → ∀[ X Θ (ctx P γ) ⇒ Y Θ (ctx Q δ) ]) →
      (∀ {P Q} → Q ≤* F .hom P → ∀[ ⟦ s ⟧s X (ctx P γ) ⇒ ⟦ s ⟧s Y (ctx Q δ) ])
    map-s (L ▹ rs) f r (l , t) = l , map-r (rs l) f r t

  module _ {X : ExtOpenFam x} {Y : ExtOpenFam y} where

    map-p′ : (ps : Premises fl) → ∀[ X ⇒ Y ] → ∀[ ⟦ ps ⟧p X ⇒ ⟦ ps ⟧p Y ]
    map-p′ ⟨ Γ `⊢ A ⟩ f t = f t
    map-p′ `⊤ f _ = _
    map-p′ `ℑ f ℑ⟨ sp ⟩ = ℑ⟨ sp ⟩
    map-p′ (ps `∧ qs) f (s , t) = map-p′ ps f s , map-p′ qs f t
    map-p′ (ps `✴ qs) f (s ✴⟨ sp ⟩ t) =
      map-p′ ps f s ✴⟨ sp ⟩ map-p′ qs f t
    map-p′ (r `· ps) f (⟨ sp ⟩· t) = ⟨ sp ⟩· map-p′ ps f t
    map-p′ (`□ ps) f (□⟨ str , sp0 , sp+ ⟩ t) =
      □⟨ str , sp0 , sp+ ⟩ map-p′ ps f t

    map-r′ : (r : Rule fl) → ∀[ X ⇒ Y ] → ∀[ ⟦ r ⟧r X ⇒ ⟦ r ⟧r Y ]
    map-r′ (ps =⇒ A) f (q , t) = q , map-p′ ps f t

    map-s′ : (s : System fl) → ∀[ X ⇒ Y ] → ∀[ ⟦ s ⟧s X ⇒ ⟦ s ⟧s Y ]
    map-s′ (L ▹ rs) f (l , t) = l , map-r′ (rs l) f t

  open import Category.Applicative

  module _ {F : Set x → Set x} {{appF : RawApplicative F}} where

    open RawApplicative appF

    sequence-p :
      ∀ {X : ExtOpenFam x} (ps : Premises fl) →
      ∀[ ⟦ ps ⟧p (λ Δ Γ B → F (X Δ Γ B)) ⇒ F ∘ ⟦ ps ⟧p X ]
    sequence-p (⟨ Γ `⊢ A ⟩) t = t
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
      ∀ {X : ExtOpenFam x} (r : Rule fl) → ∀ {A} →
      ∀[ _⟨ ⟦ r ⟧r (λ Δ Γ B → F (X Δ Γ B)) ⟩⊢ A ⇒ F ∘ _⟨ ⟦ r ⟧r X ⟩⊢ A ]
    sequence-r (ps =⇒ A) (q , t) = (q ,_) <$> sequence-p ps t

    sequence-s :
      ∀ {X : ExtOpenFam x} (s : System fl) → ∀ {A} →
      ∀[ _⟨ ⟦ s ⟧s (λ Δ Γ B → F (X Δ Γ B)) ⟩⊢ A ⇒ F ∘ _⟨ ⟦ s ⟧s X ⟩⊢ A ]
    sequence-s (L ▹ rs) (l , t) =
      (l ,_) <$> sequence-r (rs l) t
