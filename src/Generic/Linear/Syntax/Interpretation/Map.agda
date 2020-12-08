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

  LinRel : ∀ {c ℓ} (R : SkewSemiring c ℓ) (s t : LTree) → Set _
  LinRel R s t = SkewLeftSemimoduleRel
    (Vector-skewLeftSemimodule R s) (Vector-skewLeftSemimodule R t) lzero

  module _ {s t} {Γ : Vector Ty s} {Δ : Vector Ty t}
           (R : LinRel skewSemiring s t)
    where

    open SkewLeftSemimoduleRel R

    map-p : ∀ {X : Ctx → Scoped x} {Y : Ctx → Scoped y} (ps : Premises) →
            (∀ {RΘ A P Q} → rel P Q → X RΘ A (ctx P Γ) → Y RΘ A (ctx Q Δ)) →
            (∀ {P Q} → rel P Q → ⟦ ps ⟧p X (ctx P Γ) → ⟦ ps ⟧p Y (ctx Q Δ))
    map-p (⟨ PΓ `⊢ A ⟩) f r t = f r t
    map-p `⊤ f r tt = tt
    map-p `ℑ f r ℑ⟨ t ⟩ = ℑ⟨ rel-0ₘ (t , r) ⟩
    map-p (ps `∧ qs) f r (s , t) = map-p ps f r s , map-p qs f r t
    map-p (ps `✴ qs) f r (s ✴⟨ sp ⟩ t) =
      let ⟨ rs , rt ⟩ sp′ = rel-+ₘ (sp , r) in
      map-p ps f rs s ✴⟨ sp′ ⟩ map-p qs f rt t
    map-p (ρ `· ps) f r (⟨ sp ⟩· t) =
      let r′ , sp′ = rel-*ₘ (sp , r) in
      ⟨ sp′ ⟩· map-p ps f r′ t
    map-p (`□ ps) f r (□⟨ str , sp0 , sp+ ⟩ t) =
      let foo = rel-0ₘ (⊴*-trans str sp0 , r) in
      let ⟨ rl , rr ⟩ sp+′ = rel-+ₘ (⊴*-trans str sp+ , r) in
      □⟨ ⊴*-refl , foo , {!sp+′!} ⟩ map-p ps f {!r!} t
    -- map-p (`□ ps) f r (□⟨ sp0 , sp+ ⟩ t) =
    --   let sp0′ = rel-0ₘ (sp0 , r) in
    --   let ⟨ r0 , r1 ⟩ sp+′ = rel-+ₘ (sp+ , r) in
    --   □⟨ sp0′ , {!sp+′!} ⟩ map-p ps f r t

    map-r : ∀ {X : Ctx → Scoped x} {Y : Ctx → Scoped y} (r : Rule) →
            (∀ {RΘ A P Q} → rel P Q → X RΘ A (ctx P Γ) → Y RΘ A (ctx Q Δ)) →
            (∀ {A P Q} → rel P Q → ⟦ r ⟧r X A (ctx P Γ) → ⟦ r ⟧r Y A (ctx Q Δ))
    map-r (ps =⇒ A) f r (q , t) = q , map-p ps f r t

    map-s : ∀ {X : Ctx → Scoped x} {Y : Ctx → Scoped y} (s : System) →
            (∀ {RΘ A P Q} → rel P Q → X RΘ A (ctx P Γ) → Y RΘ A (ctx Q Δ)) →
            (∀ {A P Q} → rel P Q → ⟦ s ⟧s X A (ctx P Γ) → ⟦ s ⟧s Y A (ctx Q Δ))
    map-s (L ▹ rs) f r (l , t) = l , map-r (rs l) f r t

  map-s′ : ∀ {X : Ctx → Scoped x} {Y : Ctx → Scoped y} (s : System) →
           (∀ {RΘ A} → ∀[ X RΘ A ⇒ Y RΘ A ]) →
           (∀ {A} → ∀[ ⟦ s ⟧s X A ⇒ ⟦ s ⟧s Y A ])
  map-s′ s f t = map-s id-SkewLeftSemimoduleRel s (λ { ≡.refl → f }) ≡.refl t

  open import Category.Applicative

  module _ {F : Set x → Set x} {{appF : RawApplicative F}} where

    open RawApplicative appF

    sequence-p :
      ∀ {X : Ctx → Scoped x} (ps : Premises) →
      ∀[ ⟦ ps ⟧p (λ QΔ B PΓ → F (X QΔ B PΓ)) ⇒ F ∘ ⟦ ps ⟧p X ]
    sequence-p (⟨ PΓ `⊢ A ⟩) t = t
    sequence-p `⊤ tt = pure tt
    sequence-p `ℑ t = pure t
    sequence-p (ps `∧ qs) (s , t) = _,_ <$> sequence-p ps s ⊛ sequence-p qs t
    sequence-p (ps `✴ qs) (s ✴⟨ sp ⟩ t) =
      _✴⟨ sp ⟩_ <$> sequence-p ps s ⊛ sequence-p qs t
    sequence-p (ρ `· ps) (⟨ sp ⟩· t) =
      ⟨ sp ⟩·_ <$> sequence-p ps t
    sequence-p (`□ p) t = {!!}

    sequence-r :
      ∀ {X : Ctx → Scoped x} (r : Rule) →
      ∀ {A} → ∀[ ⟦ r ⟧r (λ QΔ B PΓ → F (X QΔ B PΓ)) A ⇒ F ∘ ⟦ r ⟧r X A ]
    sequence-r (ps =⇒ A) (q , t) = (q ,_) <$> sequence-p ps t

    sequence-s :
      ∀ {X : Ctx → Scoped x} (s : System) →
      ∀ {A} → ∀[ ⟦ s ⟧s (λ QΔ B PΓ → F (X QΔ B PΓ)) A ⇒ F ∘ ⟦ s ⟧s X A ]
    sequence-s (L ▹ rs) (l , t) =
      (l ,_) <$> sequence-r (rs l) t
