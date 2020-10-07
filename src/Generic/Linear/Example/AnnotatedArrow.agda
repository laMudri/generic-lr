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
  open import Data.Product as ×
  open import Data.Product.Relation.Binary.Pointwise.NonDependent as ×PW
    using (×-setoid)
  open import Data.Unit using (⊤; tt)
  open import Function.Base using (id; _∘_; _∘′_; _$_; λ-; _$-)
  open import Function.Equality using (_⟶_; _⇨_; _⟨$⟩_; cong)
  open import Size
  open import Relation.Unary
  open import Relation.Unary.Bunched
  open import Relation.Unary.Bunched.Properties
  open import Relation.Binary using (Setoid)
  open import Relation.Binary.Construct.Always as ⊤ using ()
  open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_; subst; subst₂)

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
  set .var (lvar i ≡.refl _) γ = γ .get i
  set .alg {_} {ctx P Γ} (`lam (r , A) B , ≡.refl , m) γ x =
    m {ctx P Γ ++ᶜ [ 0# , A ]ᶜ} extendʳ
      .app✴ ⊴*-refl ([-]ᵉ (⟨ ⊴*-refl ⟩· lvar (↘ here) ≡.refl ⊴*-refl))
      (γ ++₁ [ x ]₁)
  set .alg (`app rA B , ≡.refl , m ✴⟨ sp+ ⟩ (⟨ sp* ⟩· n)) γ =
    (m identity .app✴ (+*-identity↘ _) ([]ᵉ ✴1⟨ ⊴*-refl ⟩) γ)
    (n identity .app✴ (+*-identity↘ _) ([]ᵉ ✴1⟨ ⊴*-refl ⟩) γ)

  myConst : (A B : Ty) → Term ((1# , A) ⊸ (0# , B) ⊸ A) []ᶜ
  myConst A B =
    `con (`lam _ _ , ≡.refl , `con (`lam _ _ , ≡.refl ,
      `var (lvar (↙ (↘ here)) ≡.refl (([]₂ ++₂ [ ⊴-refl ]₂) ++₂ ⊴*-refl))))

  ⟦myConst⟧ : (A B : Ty) → ⟦ A ⟧ → ⟦ B ⟧ → ⟦ A ⟧
  ⟦myConst⟧ A B = semantics set {[]ᶜ} {[]ᶜ} ([]ᵉ ✴1⟨ []₂ ⟩) (myConst A B) []₁

  test : (x y : Base) → Set
  test x y = {!⟦myConst⟧ base base x y!}

  -- Setoid semantics

  ⟦_⟧ˢ : Ty → Setoid 0ℓ 0ℓ
  ⟦ base ⟧ˢ = ≡.setoid Base  -- TODO: Base should be a Setoid.
  ⟦ (_ , A) ⊸ B ⟧ˢ = ⟦ A ⟧ˢ ⇨ ⟦ B ⟧ˢ

  ⟦_⟧ˢᶜ : Ctx → Setoid 0ℓ 0ℓ
  ⟦ ctx _ Γ ⟧ˢᶜ = setoidL₁ ⟦_⟧ˢ Γ

  ⟦Tm⟧ˢ : Scoped
  ⟦Tm⟧ˢ A PΓ = ⟦ PΓ ⟧ˢᶜ ⟶ ⟦ A ⟧ˢ

  module _ where

    open Setoid

    setoid : Semantics AnnArr LVar ⟦Tm⟧ˢ
    setoid .th^𝓥 = th^LVar
    setoid .var (lvar i ≡.refl _) ⟨$⟩ γ = γ .get i
    setoid .var (lvar i ≡.refl _) .cong γγ = γγ .get i
    -- TODO: lam case could be made better by Setoid currying.
    setoid .alg {_} {ctx P Γ} (`lam (r , A) B , ≡.refl , m) ⟨$⟩ γ ⟨$⟩ x =
      m {ctx P Γ ++ᶜ [ 0# , A ]ᶜ} extendʳ
        .app✴ ⊴*-refl ([-]ᵉ (⟨ ⊴*-refl ⟩· lvar (↘ here) ≡.refl ⊴*-refl))
        ⟨$⟩ (γ ++₁ [ x ]₁)
    setoid .alg {_} {ctx P Γ} (`lam (r , A) B , ≡.refl , m) ._⟨$⟩_ γ .cong xx =
      m _ .app✴ _ _ .cong (setoidL₁ ⟦_⟧ˢ _ .refl ++₁∼ [ xx ]₁∼)
    setoid .alg (`lam rA B , ≡.refl , m) .cong γγ xx =
      m _ .app✴ _ _ .cong (γγ ++₁∼ [ xx ]₁∼)
    setoid .alg (`app rA B , ≡.refl , m ✴⟨ sp+ ⟩ (⟨ sp* ⟩· n)) ⟨$⟩ γ =
      (m identity .app✴ (+*-identity↘ _) ([]ᵉ ✴1⟨ ⊴*-refl ⟩) ⟨$⟩ γ) ⟨$⟩
      (n identity .app✴ (+*-identity↘ _) ([]ᵉ ✴1⟨ ⊴*-refl ⟩) ⟨$⟩ γ)
    setoid .alg (`app rA B , ≡.refl , m ✴⟨ sp+ ⟩ (⟨ sp* ⟩· n)) .cong γγ =
      m _ .app✴ _ _ .cong γγ (n _ .app✴ _ _ .cong γγ)

  -- Relational semantics

  record WRel (W : Set) (A : Setoid 0ℓ 0ℓ) : Set1 where
    open Setoid A
    field
      rel : (a b : Carrier) → W → Set
      resp-≈ : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → ∀[ rel a b ⇒ rel a′ b′ ]
  open WRel public

  -- TODO: move somewhere else (Relation.Unary.Extras?)

  I⋂ : ∀ {a i ℓ} {A : Set a} (I : Set i) → (I → Pred A ℓ) → Pred A _
  I⋂ I P = λ x → {i : I} → P i x

  record WRelMor {W A B} (R : WRel W A) (S : WRel W B) : Set where
    constructor wRelMor
    private
      module A = Setoid A
      module B = Setoid B
    field
      sem0 sem1 : A ⟶ B
      semsem : ∀[ (I⋂ (_ × _) \ (x , y) →
                   R .rel x y ⇒ S .rel (sem0 ⟨$⟩ x) (sem1 ⟨$⟩ y)) ]
  open WRelMor public

  module WithWorlds
    (worlds : SkewCommutativeRelMonoid 0ℓ 0ℓ)
    (open SkewCommutativeRelMonoid worlds
      renaming (Carrier to W; _≤ε to _≤0; _≤[_∙_] to _≤[_+_]))
    (open BunchedUnit _≤0 hiding (✴1⟨_⟩))
    (open BunchedConjunction _≤[_+_] hiding (_✴⟨_⟩_))
    where

    Iᴿ : WRel W (⊤.setoid ⊤ 0ℓ)
    Iᴿ .rel _ _ = ✴1
    Iᴿ .resp-≈ _ _ = id

    _⊗ᴿ_ : ∀ {A B} → WRel W A → WRel W B → WRel W (×-setoid A B)
    (R ⊗ᴿ S) .rel (xa , xb) (ya , yb) = R .rel xa ya ✴ S .rel xb yb
    (R ⊗ᴿ S) .resp-≈ (xxa , xxb) (yya , yyb) =
      map-✴ (R .resp-≈ xxa yya , S .resp-≈ xxb yyb)

  module WithStuff
    (worlds : SkewCommutativeRelMonoid 0ℓ 0ℓ)
    (open SkewCommutativeRelMonoid worlds
      renaming (Carrier to W; _≤ε to _≤0; _≤[_∙_] to _≤[_+_]))
    (open BunchedUnit _≤0 hiding (✴1⟨_⟩))
    (open BunchedConjunction _≤[_+_] hiding (_✴⟨_⟩_))
    (open WithWorlds worlds)
    (Baseᴿ : WRel W (≡.setoid Base))
    (!ᴿ : Ann → ∀[ WRel W ⇒ WRel W ])
    (!ᴿ-map : ∀ {r A B R S} (f : WRelMor R S) →
              (∀ {x y} → ∀[ !ᴿ r {A} R .rel x y ⇒
                            !ᴿ r {B} S .rel (f .sem0 ⟨$⟩ x) (f .sem1 ⟨$⟩ y) ]))
    (!ᴿ-⊴ : ∀ {r s A R x y} → r ⊴ s →
            ∀[ !ᴿ r {A} R .rel x y ⇒ !ᴿ s R .rel x y ])
    (!ᴿ-0 : ∀ {r A R x y} → r ⊴ 0# → ∀[ !ᴿ r {A} R .rel x y ⇒ ✴1 ])
    (!ᴿ-+ : ∀ {r p q A R x y} → r ⊴ p + q →
            ∀[ !ᴿ r {A} R .rel x y ⇒ !ᴿ p R .rel x y ✴ !ᴿ q R .rel x y ])
    (!ᴿ-1 : ∀ {r A R x y} → r ⊴ 1# → ∀[ !ᴿ r {A} R .rel x y ⇒ R .rel x y ])
    (!ᴿ-* : ∀ {r p q A R x y} → r ⊴ p * q →
            ∀[ !ᴿ r {A} R .rel x y ⇒ !ᴿ p (!ᴿ q R) .rel x y ])
    (!ᴿ-✴1 : ∀ {r x y} → ∀[ ✴1 ⇒ !ᴿ r Iᴿ .rel x y ])
    (!ᴿ-✴ : ∀ {r A B R S} {x@(xr , xs) : _ × _} {y@(yr , ys) : _ × _} →
            ∀[ !ᴿ r {A} R .rel xr yr ✴ !ᴿ r {B} S .rel xs ys ⇒
               !ᴿ r (R ⊗ᴿ S) .rel x y ])
    where

    open BunchedCommutativeMonoid worlds

    ⟦_⟧ᴿ : ∀ A → WRel W ⟦ A ⟧ˢ
    ⟦ base ⟧ᴿ = Baseᴿ
    ⟦ (r , A) ⊸ B ⟧ᴿ .rel f g =
      I⋂ (_ × _) \ (x , y) →
        (!ᴿ r ⟦ A ⟧ᴿ .rel x y) ─✴ ⟦ B ⟧ᴿ .rel (f ⟨$⟩ x) (g ⟨$⟩ y)
    ⟦ (r , A) ⊸ B ⟧ᴿ .resp-≈ ff gg fg .app✴ sp aa =
      ⟦ B ⟧ᴿ .resp-≈ (ff refl) (gg refl) (fg .app✴ sp aa)
      where open Setoid ⟦ A ⟧ˢ

    module ⟦_⟧ᴿᶜ where
      go : ∀ {s} R Γ → WRel W ⟦ ctx {s} R Γ ⟧ˢᶜ
      go {[-]} R Γ .rel (mk γ0) (mk γ1) =
        !ᴿ (R here) ⟦ Γ here ⟧ᴿ .rel (γ0 here) (γ1 here)
      go {[-]} R Γ .resp-≈ (mk p0) (mk p1) =
        !ᴿ (R here) ⟦ Γ here ⟧ᴿ .resp-≈ (p0 here) (p1 here)
      go {ε} R Γ .rel γ0 γ1 = ✴1
      go {ε} R Γ .resp-≈ p0 p1 = id
      go {s <+> t} R Γ .rel (mk γ0) (mk γ1) =
        go (R ∘ ↙) (Γ ∘ ↙) .rel (mk (γ0 ∘ ↙)) (mk (γ1 ∘ ↙)) ✴
        go (R ∘ ↘) (Γ ∘ ↘) .rel (mk (γ0 ∘ ↘)) (mk (γ1 ∘ ↘))
      go {s <+> t} R Γ .resp-≈ (mk p0) (mk p1) = map-✴
        ( go (R ∘ ↙) (Γ ∘ ↙) .resp-≈ (mk (p0 ∘ ↙)) (mk (p1 ∘ ↙))
        , go (R ∘ ↘) (Γ ∘ ↘) .resp-≈ (mk (p0 ∘ ↘)) (mk (p1 ∘ ↘))
        )

    ⟦_⟧ᴿᶜ : ∀ RΓ → WRel W ⟦ RΓ ⟧ˢᶜ
    ⟦ ctx R Γ ⟧ᴿᶜ = ⟦_⟧ᴿᶜ.go R Γ

    ⟦⊴⟧ᴿᶜ : ∀ {s P Q Γ} → P ⊴* Q →
            ∀ {γ0 γ1} →
            ∀[ ⟦ ctx {s} P Γ ⟧ᴿᶜ .rel γ0 γ1 ⇒ ⟦ ctx Q Γ ⟧ᴿᶜ .rel γ0 γ1 ]
    ⟦⊴⟧ᴿᶜ {[-]} (mk le) = !ᴿ-⊴ (le here)
    ⟦⊴⟧ᴿᶜ {ε} le = id
    ⟦⊴⟧ᴿᶜ {s <+> t} (mk le) =
      map-✴ (⟦⊴⟧ᴿᶜ (mk (le ∘ ↙)) , ⟦⊴⟧ᴿᶜ (mk (le ∘ ↘)))

    ⟦Tm⟧ᴿ : (A : Ty) (RΓ : Ctx) → WRel W (⟦ RΓ ⟧ˢᶜ ⇨ ⟦ A ⟧ˢ)
    ⟦Tm⟧ᴿ A RΓ .rel m0 m1 = I⋂ (_ × _) \ (γ0 , γ1) →
      ⟦ RΓ ⟧ᴿᶜ .rel γ0 γ1 ⇒ ⟦ A ⟧ᴿ .rel (m0 ⟨$⟩ γ0) (m1 ⟨$⟩ γ1)
    ⟦Tm⟧ᴿ A RΓ .resp-≈ p0 p1 mm γγ =
      ⟦ A ⟧ᴿ .resp-≈ (p0 refl) (p1 refl) (mm γγ)
      where open Setoid ⟦ RΓ ⟧ˢᶜ

    lemma-✴1 : ∀ {s R Γ γ δ} → R ⊴* 0* → ∀[ ⟦ ctx {s} R Γ ⟧ᴿᶜ .rel γ δ ⇒ ✴1 ]
    lemma-✴1 {[-]} (mk sp) = !ᴿ-0 (sp here)
    lemma-✴1 {ε} sp = id
    lemma-✴1 {s <+> t} (mk sp) =
      1-✴→ ∘ map-✴ (lemma-✴1 (mk (sp ∘ ↙)) , lemma-✴1 (mk (sp ∘ ↘)))

    lemma-✴ : ∀ {s R P Q Γ γ δ} → R ⊴* P +* Q →
              ∀[ ⟦ ctx {s} R Γ ⟧ᴿᶜ .rel γ δ ⇒
                 ⟦ ctx P Γ ⟧ᴿᶜ .rel γ δ ✴ ⟦ ctx Q Γ ⟧ᴿᶜ .rel γ δ ]
    lemma-✴ {[-]} (mk sp) = !ᴿ-+ (sp here)
    lemma-✴ {ε} sp = ✴-1←
    lemma-✴ {s <+> t} (mk sp) =
      inter-✴ ∘ map-✴ (lemma-✴ (mk (sp ∘ ↙)) , lemma-✴ (mk (sp ∘ ↘)))

    lemma-!ᴿ : ∀ {s R r Q Γ γ0 γ1} → R ⊴* r *ₗ Q →
               ∀[ ⟦ ctx {s} R Γ ⟧ᴿᶜ .rel γ0 γ1 ⇒ !ᴿ r ⟦ ctx Q Γ ⟧ᴿᶜ .rel γ0 γ1 ]
    lemma-!ᴿ {[-]} {Q = Q} {Γ} (mk sp) =
      !ᴿ _ ⟦ ctx Q Γ ⟧ᴿᶜ .resp-≈ ([-]₁η (λ {A} → refl A))
                                 ([-]₁η (λ {A} → refl A))
      ∘′ !ᴿ-map f
      ∘′ !ᴿ-* (sp here)
      where
      open module ⟦⟧ˢ A = Setoid ⟦ A ⟧ˢ

      f : WRelMor (!ᴿ (Q here) ⟦ Γ here ⟧ᴿ) ⟦ ctx Q Γ ⟧ᴿᶜ
      f .sem0 = [-]₁ˢ {S = ⟦_⟧ˢ}
      f .sem1 = [-]₁ˢ {S = ⟦_⟧ˢ}
      f .semsem = id
    lemma-!ᴿ {ε} {Q = Q} {Γ} sp = !ᴿ-map f ∘ !ᴿ-✴1
      where
      open Setoid ⟦ ctx Q Γ ⟧ˢᶜ

      f : WRelMor Iᴿ ⟦ ctx Q Γ ⟧ᴿᶜ
      f .sem0 = record { cong = λ _ → refl }
      f .sem1 = record { cong = λ _ → refl }
      f .semsem = id
    lemma-!ᴿ {s <+> t} {Q = Q} {Γ} (mk sp) =
      !ᴿ _ ⟦ ctx Q Γ ⟧ᴿᶜ .resp-≈ (++₁η (λ {A} → refl A))
                                 (++₁η (λ {A} → refl A))
      ∘′ !ᴿ-map f
      ∘′ !ᴿ-✴
      ∘′ map-✴ (lemma-!ᴿ (mk (sp ∘ ↙)) , lemma-!ᴿ (mk (sp ∘ ↘)))
      where
      open module ⟦⟧ˢ A = Setoid ⟦ A ⟧ˢ

      f : WRelMor (_ ⊗ᴿ _) ⟦ ctx Q Γ ⟧ᴿᶜ
      f .sem0 = ++₁ˢ {S = ⟦_⟧ˢ}
      f .sem1 = ++₁ˢ {S = ⟦_⟧ˢ}
      f .semsem = id

    ⟦Tm⟧ᴿ′ : Scoped
    ⟦Tm⟧ᴿ′ A RΓ = WRelMor ⟦ RΓ ⟧ᴿᶜ ⟦ A ⟧ᴿ

    wrel : Semantics AnnArr LVar ⟦Tm⟧ᴿ′
    wrel .th^𝓥 = th^LVar
    wrel .var v .sem0 = setoid .var v
    wrel .var v .sem1 = setoid .var v
    wrel .var v .semsem = go v
      where
      -- η-expand RΓ to satisfy termination checker (s gets smaller).
      go : ∀ {A s R Γ} (let RΓ = ctx {s} R Γ) (v : LVar A RΓ) →
           ∀[ ⟦Tm⟧ᴿ A RΓ .rel (setoid .var v) (setoid .var v) ]
      go (lvar here ≡.refl (mk le)) = !ᴿ-1 (le here)
      go (lvar (↙ i) ≡.refl (mk le)) =
        ✴-1→ ∘ map-✴ ( go (lvar i ≡.refl (mk (le ∘ ↙)))
                     , lemma-✴1 (mk (le ∘ ↘))
                     )
      go (lvar (↘ i) ≡.refl (mk le)) =
        1-✴→ ∘ map-✴ ( lemma-✴1 (mk (le ∘ ↙))
                     , go (lvar i ≡.refl (mk (le ∘ ↘)))
                     )
    wrel .alg mm .sem0 =
      setoid .alg (map-s′ AnnArr
                          (λ {RΓ} {A} → mapK𝓒 {𝓒 = ⟦Tm⟧ᴿ′} sem0 {RΓ} {A})
                          mm)
    wrel .alg mm .sem1 =
      setoid .alg (map-s′ AnnArr
                          (λ {RΓ} {A} → mapK𝓒 {𝓒 = ⟦Tm⟧ᴿ′} sem1 {RΓ} {A})
                          mm)
    wrel .alg {_} {ctx R Γ} (`lam (r , A) B , ≡.refl , mm) .semsem γγ .app✴ sp xx =
      mm _ .app✴ _ _ .semsem
        (⟦⊴⟧ᴿᶜ {P = R} (mk (λ i → ⊴-trans (+.identity-→ .proj₂ _)
                                          (+-mono ⊴-refl (annihil .proj₂ _))))
               γγ
         ✴⟨ sp ⟩
         !ᴿ-⊴ (⊴-trans (*.identity .proj₂ _) (+.identity-← .proj₁ _)) xx)
    wrel .alg (`app rA B , ≡.refl , mm ✴⟨ sp+ ⟩ (⟨ sp* ⟩· nn)) .semsem γγ =
      let Pγγ ✴⟨ ⟦sp+⟧ ⟩ rQγγ = lemma-✴ sp+ γγ in
      mm _ .app✴ _ _ .semsem Pγγ .app✴ ⟦sp+⟧
        (!ᴿ-map
          (nn _ .app✴ (mk λ i → +.identity-→ .proj₂ _) ([]ᵉ ✴1⟨ ⊴*-refl ⟩))
          (lemma-!ᴿ sp* rQγγ))
