{-# OPTIONS --safe --sized-types --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ)
open import Relation.Binary using (Rel)

module Generic.Linear.Example.AnnotatedArrow
  (skewSemiring : SkewSemiring 0ℓ 0ℓ) (Base : Set)
  where

  open SkewSemiring skewSemiring
    renaming (Carrier to Ann
             ; _≤_ to _⊴_
             ; refl to ⊴-refl; trans to ⊴-trans
             )

  open import Algebra.Relational
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.Product
  open import Data.Unit using (⊤; tt)
  open import Function.Base using (id; _∘_; _∘′_; _$_; λ-; _$-)
  open import Size
  open import Relation.Unary
  open import Relation.Unary.Bunched
  open import Relation.Unary.Bunched.Properties
  open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_; refl; subst; subst₂)

  infixr 5 _⊸_

  data Ty : Set where
    base : Ty
    _⊸_ : (rA : Ann × Ty) (B : Ty) → Ty

  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Algebra skewSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawSkewSemiring
  open import Generic.Linear.Syntax.Interpretation.Map Ty skewSemiring
  open import Generic.Linear.Syntax.Term Ty rawSkewSemiring
  open import Generic.Linear.Environment Ty rawSkewSemiring
    renaming (var to ivar)
  open import Generic.Linear.Thinning Ty rawSkewSemiring
  open _─Env
  open import Generic.Linear.Extend Ty skewSemiring
  open import Generic.Linear.Thinning.Properties Ty skewSemiring
  open import Generic.Linear.Environment.Properties Ty skewSemiring
  open import Generic.Linear.Semantics Ty skewSemiring

  data `AnnArr : Set where
    `lam `app : (rA : Ann × Ty) (B : Ty) → `AnnArr

  AnnArr : System
  AnnArr = system `AnnArr λ where
    (`lam rA B) → rule ([ rA ]ᶜ `⊢ B)
                       (rA ⊸ B)
    (`app rA@(r , A) B) → rule (([]ᶜ `⊢ rA ⊸ B) `* (r `· ([]ᶜ `⊢ A)))
                               B

  Term = Tm AnnArr ∞
  open WithScope (Scope Term)

  -- pattern var i les = `var (lvar i refl les)
  -- pattern lam t = `con (`lam _ _ , refl , t)

  ⟦_⟧ : Ty → Set
  ⟦ base ⟧ = Base
  ⟦ (_ , A) ⊸ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧

  ⟦_⟧ᶜ : Ctx → Set
  ⟦ ctx _ Γ ⟧ᶜ = Lift₁ ⟦_⟧ Γ

  ⟦Tm⟧ : Scoped
  ⟦Tm⟧ A PΓ = ⟦ PΓ ⟧ᶜ → ⟦ A ⟧

  open Semantics

  set : Semantics AnnArr LVar ⟦Tm⟧
  set .th^𝓥 = th^LVar
  set .var (lvar i refl _) γ = γ .get i
  set .alg {_} {ctx P Γ} (`lam (r , A) B , refl , m) γ x =
    m {ctx P Γ ++ᶜ [ 0# , A ]ᶜ} extendʳ
      .app✴ ⊴*-refl ([-]ᵉ (⟨ ⊴*-refl ⟩· lvar (↘ here) refl ⊴*-refl))
      (γ ++₁ [ x ]₁)
  set .alg (`app rA B , refl , m ✴⟨ sp+ ⟩ (⟨ sp* ⟩· n)) γ =
    (m identity .app✴ (+*-identity↘ _) ([]ᵉ ✴1⟨ ⊴*-refl ⟩) γ)
    (n identity .app✴ (+*-identity↘ _) ([]ᵉ ✴1⟨ ⊴*-refl ⟩) γ)

  myConst : (A B : Ty) → Term ((1# , A) ⊸ (0# , B) ⊸ A) []ᶜ
  myConst A B =
    `con (`lam _ _ , refl , `con (`lam _ _ , refl ,
      `var (lvar (↙ (↘ here)) refl (([]₂ ++₂ [ ⊴-refl ]₂) ++₂ ⊴*-refl))))

  ⟦myConst⟧ : (A B : Ty) → ⟦ A ⟧ → ⟦ B ⟧ → ⟦ A ⟧
  ⟦myConst⟧ A B = semantics set {[]ᶜ} {[]ᶜ} ([]ᵉ ✴1⟨ []₂ ⟩) (myConst A B) []₁

  test : (x y : Base) → Set
  test x y = {!⟦myConst⟧ base base x y!}

  -- Relational semantics

  WRel : Set → Set → Set1
  WRel W A = A → A → W → Set

  -- TODO: move somewhere else (Relation.Unary.Extras?)

  I⋂ : ∀ {a i ℓ} {A : Set a} (I : Set i) → (I → Pred A ℓ) → Pred A _
  I⋂ I P = λ x → {i : I} → P i x

  record WRelMor {W A B} (R : WRel W A) (S : WRel W B) : Set where
    constructor wRelMor
    field
      sem0 sem1 : A → B
      semsem : ∀[ (I⋂ (_ × _) \ (x , y) → R x y ⇒ S (sem0 x) (sem1 y)) ]
  open WRelMor public

  module WithStuff
    (worlds : SkewCommutativeRelMonoid 0ℓ 0ℓ)
    (open SkewCommutativeRelMonoid worlds
      renaming (Carrier to W; _≤ε to _≤0; _≤[_∙_] to _≤[_+_]))
    (open BunchedUnit _≤0 hiding (✴1⟨_⟩))
    (open BunchedConjunction _≤[_+_] hiding (_✴⟨_⟩_))
    (Baseᴿ : WRel W Base)
    (!ᴿ : Ann → ∀[ WRel W ⇒ WRel W ])
    (!ᴿ-map : ∀ {r A B R S} (f : WRelMor R S) →
              (∀ {x y} → ∀[ !ᴿ r {A} R x y ⇒ !ᴿ r {B} S (f .sem0 x) (f .sem1 y) ]))
    (!ᴿ-⊴ : ∀ {r s A R x y} → r ⊴ s → ∀[ !ᴿ r {A} R x y ⇒ !ᴿ s R x y ])
    (!ᴿ-0 : ∀ {r A R x y} → r ⊴ 0# → ∀[ !ᴿ r {A} R x y ⇒ ✴1 ])
    (!ᴿ-+ : ∀ {r p q A R x y} → r ⊴ p + q →
            ∀[ !ᴿ r {A} R x y ⇒ !ᴿ p R x y ✴ !ᴿ q R x y ])
    (!ᴿ-1 : ∀ {r A R x y} → r ⊴ 1# → ∀[ !ᴿ r {A} R x y ⇒ R x y ])
    (!ᴿ-* : ∀ {r p q A R x y} → r ⊴ p * q →
            ∀[ !ᴿ r {A} R x y ⇒ !ᴿ p (!ᴿ q R) x y ])
    (!ᴿ-✴1 : ∀ {r A x y} → ∀[ ✴1 ⇒ !ᴿ r {A} (λ _ _ → ✴1) x y ])
    (!ᴿ-✴ : ∀ {r A B R S} {x@(xr , xs) : _ × _} {y@(yr , ys) : _ × _} →
            ∀[ !ᴿ r {A} R xr yr ✴ !ᴿ r {B} S xs ys ⇒
               !ᴿ r (λ (xr , xs) (yr , ys) → R xr yr ✴ S xs ys) x y ])
    where

    -- open BunchedScaling _≤[_*ₗ_] hiding (⟨_⟩·_)
    open BunchedCommutativeMonoid worlds

    ⟦_⟧ᴿ : ∀ A → WRel W ⟦ A ⟧
    ⟦ base ⟧ᴿ = Baseᴿ
    ⟦ (r , A) ⊸ B ⟧ᴿ f g =
      I⋂ (_ × _) \ (x , y) → (!ᴿ r ⟦ A ⟧ᴿ x y) ─✴ ⟦ B ⟧ᴿ (f x) (g y)

    module ⟦_⟧ᴿᶜ where
      go : ∀ {s} R Γ → WRel W ⟦ ctx {s} R Γ ⟧ᶜ
      go {[-]} R Γ γ δ = !ᴿ (R here) ⟦ Γ here ⟧ᴿ (γ .get here) (δ .get here)
      go {ε} R Γ γ δ = ✴1
      go {s <+> t} R Γ γ δ =
        go (R ∘ ↙) (Γ ∘ ↙) (mk (γ .get ∘ ↙)) (mk (δ .get ∘ ↙)) ✴
        go (R ∘ ↘) (Γ ∘ ↘) (mk (γ .get ∘ ↘)) (mk (δ .get ∘ ↘))

    ⟦_⟧ᴿᶜ : ∀ RΓ → WRel W ⟦ RΓ ⟧ᶜ
    ⟦ ctx R Γ ⟧ᴿᶜ = ⟦_⟧ᴿᶜ.go R Γ

    ⟦⊴⟧ᴿᶜ : ∀ {s P Q Γ} → P ⊴* Q →
            ∀ {γ0 γ1} → ∀[ ⟦ ctx {s} P Γ ⟧ᴿᶜ γ0 γ1 ⇒ ⟦ ctx Q Γ ⟧ᴿᶜ γ0 γ1 ]
    ⟦⊴⟧ᴿᶜ {[-]} (mk le) = !ᴿ-⊴ (le here)
    ⟦⊴⟧ᴿᶜ {ε} le = id
    ⟦⊴⟧ᴿᶜ {s <+> t} (mk le) =
      map-✴ (⟦⊴⟧ᴿᶜ (mk (le ∘ ↙)) , ⟦⊴⟧ᴿᶜ (mk (le ∘ ↘)))

    ⟦Tm⟧ᴿ : (A : Ty) (RΓ : Ctx) → WRel W (⟦Tm⟧ A RΓ)
    ⟦Tm⟧ᴿ A RΓ m n = I⋂ (_ × _) \ (γ , δ) → ⟦ RΓ ⟧ᴿᶜ γ δ ⇒ ⟦ A ⟧ᴿ (m γ) (n δ)

    lemma-✴1 : ∀ {s R Γ γ δ} → R ⊴* 0* → ∀[ ⟦ ctx {s} R Γ ⟧ᴿᶜ γ δ ⇒ ✴1 ]
    lemma-✴1 {[-]} (mk sp) = !ᴿ-0 (sp here)
    lemma-✴1 {ε} sp = id
    lemma-✴1 {s <+> t} (mk sp) =
      1-✴→ ∘ map-✴ (lemma-✴1 (mk (sp ∘ ↙)) , lemma-✴1 (mk (sp ∘ ↘)))

    lemma-✴ : ∀ {s R P Q Γ γ δ} → R ⊴* P +* Q →
              ∀[ ⟦ ctx {s} R Γ ⟧ᴿᶜ γ δ ⇒ ⟦ ctx P Γ ⟧ᴿᶜ γ δ ✴ ⟦ ctx Q Γ ⟧ᴿᶜ γ δ ]
    lemma-✴ {[-]} (mk sp) = !ᴿ-+ (sp here)
    lemma-✴ {ε} sp = ✴-1←
    lemma-✴ {s <+> t} (mk sp) =
      inter-✴ ∘ map-✴ (lemma-✴ (mk (sp ∘ ↙)) , lemma-✴ (mk (sp ∘ ↘)))

    lemma-!ᴿ : ∀ {s R r Q Γ γ0 γ1} → R ⊴* r *ₗ Q →
               ∀[ ⟦ ctx {s} R Γ ⟧ᴿᶜ γ0 γ1 ⇒ !ᴿ r ⟦ ctx Q Γ ⟧ᴿᶜ γ0 γ1 ]
    lemma-!ᴿ {[-]} {Q = Q} {Γ} (mk sp) =
      subst₂ (λ γ0 γ1 → !ᴿ _ _ γ0 γ1 _) {!!} {!!}
      ∘′ !ᴿ-map {R = !ᴿ (Q here) ⟦ Γ here ⟧ᴿ}
                {λ (γ0 : ⟦ ctx Q Γ ⟧ᶜ) (γ1 : ⟦ ctx Q Γ ⟧ᶜ) →
                   !ᴿ (Q here) ⟦ Γ here ⟧ᴿ (γ0 .get here) (γ1 .get here)}
                (wRelMor [_]₁ [_]₁ id)
      ∘′ !ᴿ-* (sp here)
    lemma-!ᴿ {ε} sp = !ᴿ-✴1
    lemma-!ᴿ {s <+> t} (mk sp) =
      subst₂ (λ γ0 γ1 → !ᴿ _ _ γ0 γ1 _) {!!} {!!}
      ∘′ !ᴿ-map (wRelMor (uncurry _++₁_) (uncurry _++₁_) id)
      ∘′ !ᴿ-✴
      ∘′ map-✴ (lemma-!ᴿ (mk (sp ∘ ↙)) , lemma-!ᴿ (mk (sp ∘ ↘)))

    ⟦Tm⟧ᴿ′ : Ty → Ctx → Set
    ⟦Tm⟧ᴿ′ A RΓ = WRelMor ⟦ RΓ ⟧ᴿᶜ ⟦ A ⟧ᴿ

    wrel : Semantics AnnArr LVar ⟦Tm⟧ᴿ′
    wrel .th^𝓥 = th^LVar
    wrel .var v .sem0 = set .var v
    wrel .var v .sem1 = set .var v
    wrel .var v .semsem = go v
      where
      -- η-expand RΓ to satisfy termination checker (s gets smaller).
      go : ∀ {A s R Γ} (let RΓ = ctx {s} R Γ) (v : LVar A RΓ) →
           ∀[ ⟦Tm⟧ᴿ A RΓ (set .var v) (set .var v) ]
      go (lvar here ≡.refl (mk le)) = !ᴿ-1 (le here)
      go (lvar (↙ i) ≡.refl (mk le)) =
        ✴-1→ ∘ map-✴ ( go (lvar i ≡.refl (mk (le ∘ ↙)))
                     , lemma-✴1 (mk (le ∘ ↘))
                     )
      go (lvar (↘ i) ≡.refl (mk le)) =
        1-✴→ ∘ map-✴ ( lemma-✴1 (mk (le ∘ ↙))
                     , go (lvar i ≡.refl (mk (le ∘ ↘)))
                     )
    wrel .alg mm .sem0 = set .alg (map-s′ AnnArr (mapK𝓒 {𝓒 = ⟦Tm⟧ᴿ′} sem0) mm)
    wrel .alg mm .sem1 = set .alg (map-s′ AnnArr (mapK𝓒 {𝓒 = ⟦Tm⟧ᴿ′} sem1) mm)
    wrel .alg {_} {ctx R Γ} (`lam rA B , refl , mm) .semsem γγ .app✴ sp xx =
      mm _ .app✴ _ _ .semsem
        (⟦⊴⟧ᴿᶜ {P = R} (mk λ i → ⊴-trans (+.identity-→ .proj₂ _)
                                         (+-mono ⊴-refl (annihil .proj₂ _)))
               γγ
         ✴⟨ sp ⟩
         !ᴿ-⊴ (⊴-trans (*.identity .proj₂ _) (+.identity-← .proj₁ _)) xx)
    wrel .alg (`app rA B , refl , mm ✴⟨ sp+ ⟩ (⟨ sp* ⟩· nn)) .semsem γγ =
      let Pγγ ✴⟨ ⟦sp+⟧ ⟩ rQγγ = lemma-✴ sp+ γγ in
      mm _ .app✴ _ _ .semsem Pγγ .app✴ ⟦sp+⟧
        (!ᴿ-map
          (nn _ .app✴ (mk λ i → +.identity-→ .proj₂ _) ([]ᵉ ✴1⟨ ⊴*-refl ⟩))
          (lemma-!ᴿ sp* rQγγ))
