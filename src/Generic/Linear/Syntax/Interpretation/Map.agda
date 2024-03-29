{-# OPTIONS --safe --without-K --prop --postfix-projections #-}

open import Algebra.Po
open import Level using (Level; 0ℓ)

module Generic.Linear.Syntax.Interpretation.Map
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open import Algebra.Po.Relation
  open import Algebra.Po.Construct.Vector
  open import Algebra.Relational
  open import Algebra.Relational.Relation
  open import Data.Bool.Extra
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

  module _ {ℓ s t} {γ : Vector Ty s} {δ : Vector Ty t}
           (F : LinFuncRel s t ℓ) {X : ExtOpenFam x} {Y : ExtOpenFam y}
    where

    -- open RelLeftSemimoduleRel F

    map-p : (ps : Premises fl) →
      (∀ {Θ P Q} → F .rel P Q → ∀[ X Θ (ctx P γ) ⇒ Y Θ (ctx Q δ) ]) →
      (∀ {P Q} → F .rel P Q → ⟦ ps ⟧p X (ctx P γ) → ⟦ ps ⟧p Y (ctx Q δ))
    map-p ⟨ Γ `⊢ A ⟩ f r M = f r M
    map-p `⊤ f r _ = _
    map-p (ps `∧ qs) f r (M , N) = map-p ps f r M , map-p qs f r N
    map-p `ℑ f r ℑ⟨ sp0 ⟩ = ℑ⟨ F .rel-0ₘ (sp0 , r) ⟩
    map-p (ps `✴ qs) f r (M ✴⟨ sp+ ⟩ N) =
      let rM ↘, sp+′ ,↙ rN = F .rel-+ₘ (sp+ , r) in
      map-p ps f rM M ✴⟨ sp+′ ⟩ map-p qs f rN N
    map-p (p `· ps) f r (⟨ sp* ⟩· M) =
      let r′ , sp*′ = F .rel-*ₘ (sp* , r) in
      ⟨ sp*′ ⟩· map-p ps f r′ M
    map-p (`□ bf ps) f {P} {Q} P∼Q (□⟨_,_,_,_⟩_ {P′} str sp0 sp+ sp* M) =
      let _,_ {Q′} P′∼Q′ uQ′ = F .func P′ in
      let open BoxFlags bf in
      let
        P′∼Q : F .rel P′ Q
        P′∼Q = F .rel-≤ₘ str ≤*-refl P∼Q
        Q≤Q′ : Q ≤* Q′
        Q≤Q′ = uQ′ P′∼Q
        sp0′ : If p0 (Q′ ≤0*)
        sp0′ = for-If sp0 λ sp0 → F .rel-0ₘ (sp0 , P′∼Q′)
        sp+′ : If p+ (Q′ ≤[ Q′ +* Q′ ])
        sp+′ = for-If sp+ λ sp+ →
          let rl ↘, sp ,↙ rr = F .rel-+ₘ (sp+ , P′∼Q′) in
          +ₘ-mono ≤*-refl (F .func _ .unique rl) (F .func _ .unique rr) sp
        sp*′ : If p* (∀ s → Q′ ≤[ s *ₗ Q′ ])
        sp*′ = for-If sp* λ sp* s →
          let r′ , sp = F .rel-*ₘ (sp* s , P′∼Q′) in
          *ₘ-mono ≤*-refl ≤-refl (F .func _ .unique r′) sp
      in
      □⟨ Q≤Q′ , sp0′ , sp+′ , sp*′ ⟩ map-p ps f P′∼Q′ M

    map-r : (r : Rule fl) →
      (∀ {Θ P Q} → F .rel P Q → ∀[ X Θ (ctx P γ) ⇒ Y Θ (ctx Q δ) ]) →
      (∀ {P Q} → F .rel P Q → ∀[ ⟦ r ⟧r X (ctx P γ) ⇒ ⟦ r ⟧r Y (ctx Q δ) ])
    map-r (ps =⇒ A) f r (q , M) = q , map-p ps f r M

    map-s : (s : System fl) →
      (∀ {Θ P Q} → F .rel P Q → ∀[ X Θ (ctx P γ) ⇒ Y Θ (ctx Q δ) ]) →
      (∀ {P Q} → F .rel P Q → ∀[ ⟦ s ⟧s X (ctx P γ) ⇒ ⟦ s ⟧s Y (ctx Q δ) ])
    map-s (L ▹ rs) f r (l , M) = l , map-r (rs l) f r M

  module _ {X : ExtOpenFam x} {Y : ExtOpenFam y} where

    map-p′ : (ps : Premises fl) → ∀[ X ⇒ Y ] → ∀[ ⟦ ps ⟧p X ⇒ ⟦ ps ⟧p Y ]
    map-p′ ⟨ Γ `⊢ A ⟩ f t = f t
    map-p′ `⊤ f _ = _
    map-p′ `ℑ f ℑ⟨ sp ⟩ = ℑ⟨ sp ⟩
    map-p′ (ps `∧ qs) f (s , t) = map-p′ ps f s , map-p′ qs f t
    map-p′ (ps `✴ qs) f (s ✴⟨ sp ⟩ t) =
      map-p′ ps f s ✴⟨ sp ⟩ map-p′ qs f t
    map-p′ (r `· ps) f (⟨ sp ⟩· t) = ⟨ sp ⟩· map-p′ ps f t
    map-p′ (`□ bf ps) f (□⟨ str , sp0 , sp+ , sp* ⟩ t) =
      □⟨ str , sp0 , sp+ , sp* ⟩ map-p′ ps f t

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
    sequence-p (`□ bf ps) (□⟨ str , sp0 , sp+ , sp* ⟩ t) =
      □⟨ str , sp0 , sp+ , sp* ⟩_ <$> sequence-p ps t

    sequence-r :
      ∀ {X : ExtOpenFam x} (r : Rule fl) → ∀ {A} →
      ∀[ _⟨ ⟦ r ⟧r (λ Δ Γ B → F (X Δ Γ B)) ⟩⊢ A ⇒ F ∘ _⟨ ⟦ r ⟧r X ⟩⊢ A ]
    sequence-r (ps =⇒ A) (q , t) = (q ,_) <$> sequence-p ps t

    sequence-s :
      ∀ {X : ExtOpenFam x} (s : System fl) → ∀ {A} →
      ∀[ _⟨ ⟦ s ⟧s (λ Δ Γ B → F (X Δ Γ B)) ⟩⊢ A ⇒ F ∘ _⟨ ⟦ s ⟧s X ⟩⊢ A ]
    sequence-s (L ▹ rs) (l , t) =
      (l ,_) <$> sequence-r (rs l) t
