{-# OPTIONS --safe --sized-types --without-K --postfix-projections --prop #-}

open import Algebra.Po
open import Level using (0ℓ)
open import Relation.Binary using (Rel)

module Generic.Linear.Example.AnnotatedArrow
  (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ) (Base : Set)
  where

  open PoSemiring poSemiring
    hiding (setoid)
    renaming (Carrier to Ann
             ; _≤_ to _⊴_
             ; ≤-refl to ⊴-refl; ≤-trans to ⊴-trans
             )

  open import Algebra.Relational
  open import Data.LTree
  open import Data.LTree.Vector hiding (setoid)
  open import Data.LTree.Matrix
  open import Data.Product as ×
  open import Data.Product.Relation.Binary.Pointwise.NonDependent as ×PW
    using (×-setoid)
  open import Data.Unit using (⊤; tt)
  open import Data.Wrap
  open import Function.Base using (id; _∘_; _∘′_; _$_; λ-; _$-)
  open import Function.Equality using (_⟶_; _⇨_; _⟨$⟩_; cong)
  open import Proposition
  open import Size
  open import Relation.Nary
  open import Relation.Unary.Checked as Chk using (Pred)
  open import Relation.Unary.Bunched.Checked
  open import Relation.Unary.Bunched.Properties
  open import Relation.Binary using (Setoid)
  open import Relation.Binary.Construct.Always as ⊤ using ()
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

  infixr 5 _⊸_

  data Ty : Set where
    base : Ty
    _⊸_ : (rA : Ann × Ty) (B : Ty) → Ty

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring
  open import Generic.Linear.Syntax.Interpretation.Map Ty poSemiring
  open import Generic.Linear.Syntax.Term Ty rawPoSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Environment Ty poSemiring
  open import Generic.Linear.Renaming Ty poSemiring
  open [_]_⇒ᵉ_
  open import Generic.Linear.Extend Ty poSemiring
  open import Generic.Linear.Renaming.Properties Ty poSemiring
  open import Generic.Linear.Environment.Properties Ty poSemiring
  open import Generic.Linear.Semantics Ty poSemiring

  data `AnnArr : Set where
    `lam `app : (rA : Ann × Ty) (B : Ty) → `AnnArr

  flags : PremisesFlags
  flags = record noPremisesFlags { Has-✴ = ⊤ᴾ ; Has-· = ⊤ᴾ }

  AnnArr : System flags
  AnnArr = `AnnArr ▹ λ where
    (`lam rA B) → ⟨ [ rA ]ᶜ `⊢ B ⟩ =⇒ rA ⊸ B
    (`app rA@(r , A) B) → ⟨ []ᶜ `⊢ rA ⊸ B ⟩ `✴ r `· ⟨ []ᶜ `⊢ A ⟩ =⇒ B

  Term = [ AnnArr , ∞ ]_⊢_
  open WithScope (Scope Term)

  -- pattern var i les = `var (lvar i refl les)
  -- pattern lam t = `con (`lam _ _ , refl , t)

  ⟦_⟧ : Ty → Set
  ⟦ base ⟧ = Base
  ⟦ (_ , A) ⊸ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧

  ⟦_⟧ᶜ : Ctx → Set
  ⟦ ctx _ γ ⟧ᶜ = Lift₁ ⟦_⟧ γ

  ⟦Tm⟧ : Scoped 0ℓ
  ⟦Tm⟧ Γ A = ⟦ Γ ⟧ᶜ → ⟦ A ⟧

  open Semantics
  open With-psh^𝓥 (λ {s} {γ} {P} {Q} → psh^∋ {s} {γ} {P} {Q})

  set : Semantics AnnArr _∋_ ⟦Tm⟧
  set .ren^𝓥 = ren^∋
  set .var (lvar i ≡.refl _) γ0 = γ0 .get i
  set .alg {ctx P γ} (`lam (r , A) B , ≡.refl , m) γ0 x =
    m .get {ctx P γ ++ᶜ [ 0# , A ]ᶜ} extendʳ
      .app✴ +*-triv ([-]ᵉ (⟨ *ₗ-triv ⟩· lvar (↘ here) ≡.refl ⊴*-refl))
      (γ0 ++₁ [ x ]₁)
  set .alg (`app rA B , ≡.refl , m ✴⟨ sp+ ⟩ (⟨ sp* ⟩· n)) γ0 =
    (m .get identity .app✴ (+*-identity↘ _) ([]ᵉ ℑ⟨ 0*-triv ⟩) γ0)
    (n .get identity .app✴ (+*-identity↘ _) ([]ᵉ ℑ⟨ 0*-triv ⟩) γ0)

  myConst : (A B : Ty) → Term []ᶜ ((1# , A) ⊸ (0# , B) ⊸ A)
  myConst A B =
    `con (`lam _ _ , ≡.refl , `con (`lam _ _ , ≡.refl ,
      `var (lvar (↙ (↘ here)) ≡.refl (([]ₙ ++ₙ [ ⊴-refl ]ₙ) ++ₙ ⊴*-refl))))

  ⟦myConst⟧ : (A B : Ty) → ⟦ A ⟧ → ⟦ B ⟧ → ⟦ A ⟧
  ⟦myConst⟧ A B = semantics set {[]ᶜ} {[]ᶜ} ([]ᵉ ℑ⟨ []ₙ ⟩) (myConst A B) []₁

  test : (x y : Base) → ⟦myConst⟧ base base x y ≡ x
  test x y = ≡.refl

  -- Setoid semantics

  ⟦_⟧ˢ : Ty → Setoid 0ℓ 0ℓ
  ⟦ base ⟧ˢ = ≡.setoid Base  -- TODO: Base should be a Setoid.
  ⟦ (_ , A) ⊸ B ⟧ˢ = ⟦ A ⟧ˢ ⇨ ⟦ B ⟧ˢ

  ⟦_⟧ˢᶜ : Ctx → Setoid 0ℓ 0ℓ
  ⟦ ctx _ γ ⟧ˢᶜ = setoidL₁ ⟦_⟧ˢ γ

  ⟦Tm⟧ˢ : Scoped 0ℓ
  ⟦Tm⟧ˢ Γ A = ⟦ Γ ⟧ˢᶜ ⟶ ⟦ A ⟧ˢ

  module _ where

    open Setoid

    setoid : Semantics AnnArr _∋_ ⟦Tm⟧ˢ
    setoid .ren^𝓥 = ren^∋
    setoid .var (lvar i ≡.refl _) ⟨$⟩ γ0 = γ0 .get i
    setoid .var (lvar i ≡.refl _) .cong γγ = γγ .get i
    -- TODO: lam case could be made better by Setoid currying.
    setoid .alg {ctx P γ} (`lam (r , A) B , ≡.refl , m) ⟨$⟩ γ0 ⟨$⟩ x =
      m .get {ctx P γ ++ᶜ [ 0# , A ]ᶜ} extendʳ
        .app✴ +*-triv ([-]ᵉ (⟨ *ₗ-triv ⟩· lvar (↘ here) ≡.refl ⊴*-refl))
        ⟨$⟩ (γ0 ++₁ [ x ]₁)
    setoid .alg {ctx P γ} (`lam (r , A) B , ≡.refl , m) ._⟨$⟩_ γ0 .cong xx =
      m .get _ .app✴ _ _ .cong (setoidL₁ ⟦_⟧ˢ _ .refl ++₁∼ [ xx ]₁∼)
    setoid .alg (`lam rA B , ≡.refl , m) .cong γγ xx =
      m .get _ .app✴ _ _ .cong (γγ ++₁∼ [ xx ]₁∼)
    setoid .alg (`app rA B , ≡.refl , m ✴⟨ sp+ ⟩ (⟨ sp* ⟩· n)) ⟨$⟩ γ0 =
      (m .get identity .app✴ (+*-identity↘ _) ([]ᵉ ℑ⟨ 0*-triv ⟩) ⟨$⟩ γ0) ⟨$⟩
      (n .get identity .app✴ (+*-identity↘ _) ([]ᵉ ℑ⟨ 0*-triv ⟩) ⟨$⟩ γ0)
    setoid .alg (`app rA B , ≡.refl , m ✴⟨ sp+ ⟩ (⟨ sp* ⟩· n)) .cong γγ =
      m .get _ .app✴ _ _ .cong γγ (n .get _ .app✴ _ _ .cong γγ)

  -- Relational semantics

  record WRel {W : Set} (_≤_ : Rel W 0ℓ) (A : Setoid 0ℓ 0ℓ) : Set₁ where
    private module A = Setoid A
    field
      rel : (a b : A.Carrier) → W → Set
      resp-≈ : ∀ {a a′ b b′} → a A.≈ a′ → b A.≈ b′ → ∀[ rel a b ⇒ rel a′ b′ ]
      subres : ∀ {a b w w′} → w′ ≤ w → rel a b w → rel a b w′
  open WRel public

  -- TODO: move somewhere else (Relation.Unary.Extras?)

  I⋂ : ∀ {a i ℓ} {A : Set a} (I : Set i) → (I → Pred A ℓ) → Pred A _
  I⋂ I P = λ x → {i : I} → P i x

  record WRelMor {W ≤ A B} (R : WRel {W} ≤ A) (S : WRel ≤ B) : Set where
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
    (worlds : CommutativeRelMonoid 0ℓ 0ℓ)
    (open CommutativeRelMonoid worlds renaming (Carrier to W; refl to ≤-refl))
    (open BunchedUnit _≤ε hiding (ℑ⟨_⟩))
    (open BunchedConjunction _≤[_∙_])
    where

    Iᴿ : WRel _≤_ (⊤.setoid ⊤ 0ℓ)
    Iᴿ .rel _ _ = ℑ
    Iᴿ .resp-≈ _ _ = id
    Iᴿ .subres sub ℑ⟨ sp ⟩ = ℑ⟨ ε-mono sub sp ⟩

    _⊗ᴿ_ : ∀ {A B} → WRel _≤_ A → WRel _≤_ B → WRel _≤_ (×-setoid A B)
    (R ⊗ᴿ S) .rel (xa , xb) (ya , yb) = R .rel xa ya ✴ S .rel xb yb
    (R ⊗ᴿ S) .resp-≈ (xxa , xxb) (yya , yyb) =
      map-✴ (R .resp-≈ xxa yya , S .resp-≈ xxb yyb)
    (R ⊗ᴿ S) .subres sub (r ✴⟨ sp ⟩ s) = r ✴⟨ ∙-mono sub ≤-refl ≤-refl sp ⟩ s

  module WithStuff
    (worlds : CommutativeRelMonoid 0ℓ 0ℓ)
    (open CommutativeRelMonoid worlds renaming
      (Carrier to W; refl to ≤-refl; trans to ≤-trans))
    (open BunchedOrder _≤_)
    (open BunchedUnit _≤ε hiding (ℑ⟨_⟩))
    (open BunchedConjunction _≤[_∙_])
    (open WithWorlds worlds)
    (Baseᴿ : WRel _≤_ (≡.setoid Base))
    (!ᴿ : Ann → ∀[ WRel _≤_ ⇒ WRel _≤_ ])
    (!ᴿ-≤ : ∀ {r A R x y w w′} → w′ ≤ w →
      !ᴿ r {A} R .rel x y w → !ᴿ r {A} R .rel x y w′)
    (!ᴿ-map : ∀ {r A B R S} (f : WRelMor R S) → ∀ {x y} →
      ∀[ !ᴿ r {A} R .rel x y ⇒
         !ᴿ r {B} S .rel (f .sem0 ⟨$⟩ x) (f .sem1 ⟨$⟩ y) ])
    (!ᴿ-⊴ : ∀ {r s A R x y} → r ⊴ s →
      ∀[ !ᴿ r {A} R .rel x y ⇒ !ᴿ s R .rel x y ])
    (!ᴿ-0 : ∀ {r A R x y} → r ⊴ 0# → ∀[ !ᴿ r {A} R .rel x y Chk.⇒ ℑ ])
    (!ᴿ-+ : ∀ {r p q A R x y} → r ⊴ p + q →
      ∀[ !ᴿ r {A} R .rel x y ⇒ !ᴿ p R .rel x y ✴ !ᴿ q R .rel x y ])
    (!ᴿ-1 : ∀ {r A R x y} → r ⊴ 1# → ∀[ !ᴿ r {A} R .rel x y ⇒ R .rel x y ])
    (!ᴿ-* : ∀ {r p q A R x y} → r ⊴ p * q →
      ∀[ !ᴿ r {A} R .rel x y ⇒ !ᴿ p (!ᴿ q R) .rel x y ])
    (!ᴿ-ℑ : ∀ {r x y} → ∀[ ℑ ⇒ !ᴿ r Iᴿ .rel x y ])
    (!ᴿ-✴ : ∀ {r A B R S} {x@(xr , xs) : _ × _} {y@(yr , ys) : _ × _} →
      ∀[ !ᴿ r {A} R .rel xr yr ✴ !ᴿ r {B} S .rel xs ys ⇒
         !ᴿ r (R ⊗ᴿ S) .rel x y ])
    where

    open BunchedCommutativeMonoid worlds

    ⟦_⟧ᴿ : ∀ A → WRel _≤_ ⟦ A ⟧ˢ
    ⟦ base ⟧ᴿ = Baseᴿ
    ⟦ (r , A) ⊸ B ⟧ᴿ .rel f g =
      I⋂ (_ × _) \ (x , y) →
        (!ᴿ r ⟦ A ⟧ᴿ .rel x y) ─✴ ⟦ B ⟧ᴿ .rel (f ⟨$⟩ x) (g ⟨$⟩ y)
    ⟦ (r , A) ⊸ B ⟧ᴿ .resp-≈ ff gg fg .app✴ sp aa =
      ⟦ B ⟧ᴿ .resp-≈ (ff A.refl) (gg A.refl) (fg .app✴ sp aa)
      where module A = Setoid ⟦ A ⟧ˢ
    ⟦ (r , A) ⊸ B ⟧ᴿ .subres sub rf .app✴ sp aa =
      rf .app✴ (∙-mono ≤-refl sub ≤-refl sp) aa

    module ⟦_⟧ᴿᶜ where
      go : ∀ {s} R γ → WRel _≤_ ⟦ ctx {s} R γ ⟧ˢᶜ

      go {[-]} R γ .rel (mk γ0) (mk γ1) =
        !ᴿ (R here) ⟦ γ here ⟧ᴿ .rel (γ0 here) (γ1 here)
      go {[-]} R γ .resp-≈ (mk p0) (mk p1) =
        !ᴿ (R here) ⟦ γ here ⟧ᴿ .resp-≈ (p0 here) (p1 here)
      go {[-]} R γ .subres sub r = !ᴿ-≤ sub r

      go {ε} R γ .rel γ0 γ1 = ℑ
      go {ε} R γ .resp-≈ p0 p1 = id
      go {ε} R γ .subres sub ℑ⟨ sp ⟩ = ℑ⟨ ε-mono sub sp ⟩

      go {s <+> t} R γ .rel (mk γ0) (mk γ1) =
        go (R ∘ ↙) (γ ∘ ↙) .rel (mk (γ0 ∘ ↙)) (mk (γ1 ∘ ↙)) ✴
        go (R ∘ ↘) (γ ∘ ↘) .rel (mk (γ0 ∘ ↘)) (mk (γ1 ∘ ↘))
      go {s <+> t} R γ .resp-≈ (mk p0) (mk p1) = map-✴
        ( go (R ∘ ↙) (γ ∘ ↙) .resp-≈ (mk (p0 ∘ ↙)) (mk (p1 ∘ ↙))
        , go (R ∘ ↘) (γ ∘ ↘) .resp-≈ (mk (p0 ∘ ↘)) (mk (p1 ∘ ↘))
        )
      go {s <+> t} R γ .subres sub (rl ✴⟨ sp ⟩ rr) =
        rl ✴⟨ ∙-mono sub ≤-refl ≤-refl sp ⟩ rr

    ⟦_⟧ᴿᶜ : ∀ Rγ → WRel _≤_ ⟦ Rγ ⟧ˢᶜ
    ⟦ ctx R γ ⟧ᴿᶜ = ⟦_⟧ᴿᶜ.go R γ

    ⟦⊴⟧ᴿᶜ : ∀ {s P Q γ} → P ⊴* Q →
      ∀[ ⟦ ctx {s} P γ ⟧ᴿᶜ .rel ⇒ ⟦ ctx Q γ ⟧ᴿᶜ .rel ]
    ⟦⊴⟧ᴿᶜ {[-]} (mk le) = !ᴿ-⊴ (le here)
    ⟦⊴⟧ᴿᶜ {ε} le = id
    ⟦⊴⟧ᴿᶜ {s <+> t} (mk le) =
      map-✴ (⟦⊴⟧ᴿᶜ (mk (le ∘ ↙)) , ⟦⊴⟧ᴿᶜ (mk (le ∘ ↘)))

    {- Interesting, but unnecessary
    ⟦Tm⟧ᴿ : (A : Ty) (Rγ : Ctx) → WRel _≤_ (⟦ Rγ ⟧ˢᶜ ⇨ ⟦ A ⟧ˢ)
    ⟦Tm⟧ᴿ A Rγ .rel m0 m1 = I⋂ (_ × _) \ (γ0 , γ1) →
      ⟦ Rγ ⟧ᴿᶜ .rel γ0 γ1 ⇒ᵏ ⟦ A ⟧ᴿ .rel (m0 ⟨$⟩ γ0) (m1 ⟨$⟩ γ1)
    ⟦Tm⟧ᴿ A Rγ .resp-≈ p0 p1 mm le γγ =
      ⟦ A ⟧ᴿ .resp-≈ (p0 Rγ.refl) (p1 Rγ.refl) (mm le γγ)
      where module Rγ = Setoid ⟦ Rγ ⟧ˢᶜ
    ⟦Tm⟧ᴿ A Rγ .subres sub mm le γγ = mm (≤-trans le sub) γγ
    -}

    ⟦Tm⟧-rel : (A : Ty) (Rγ : Ctx) (m0 m1 : ⟦ Rγ ⟧ˢᶜ ⟶ ⟦ A ⟧ˢ) → W → Set
    ⟦Tm⟧-rel A Rγ m0 m1 = I⋂ (_ × _) \ (γ0 , γ1) →
      ⟦ Rγ ⟧ᴿᶜ .rel γ0 γ1 ⇒ ⟦ A ⟧ᴿ .rel (m0 ⟨$⟩ γ0) (m1 ⟨$⟩ γ1)

    lemma-ℑ : ∀ {s R γ γ0 γ1} → R ⊴0* →
      ∀[ ⟦ ctx {s} R γ ⟧ᴿᶜ .rel γ0 γ1 Chk.⇒ ℑ ]
    lemma-ℑ {[-]} (mk sp) = !ᴿ-0 (sp here)
    lemma-ℑ {ε} sp = id
    lemma-ℑ {s <+> t} (mk sp) =
      1✴1→ ∘ map-✴ (lemma-ℑ (mk (sp ∘ ↙)) , lemma-ℑ (mk (sp ∘ ↘)))

    lemma-✴ : ∀ {s R P Q γ γ0 γ1} → R ⊴[ P +* Q ] →
      ∀[ ⟦ ctx {s} R γ ⟧ᴿᶜ .rel γ0 γ1 ⇒
         ⟦ ctx P γ ⟧ᴿᶜ .rel γ0 γ1 ✴ ⟦ ctx Q γ ⟧ᴿᶜ .rel γ0 γ1 ]
    lemma-✴ {[-]} (mk sp) = !ᴿ-+ (sp here)
    lemma-✴ {ε} sp = 1✴1←
    lemma-✴ {s <+> t} (mk sp) =
      inter-✴ ∘ map-✴ (lemma-✴ (mk (sp ∘ ↙)) , lemma-✴ (mk (sp ∘ ↘)))

    lemma-!ᴿ : ∀ {s R r Q γ γ0 γ1} → R ⊴[ r *ₗ Q ] →
      ∀[ ⟦ ctx {s} R γ ⟧ᴿᶜ .rel γ0 γ1 ⇒ !ᴿ r ⟦ ctx Q γ ⟧ᴿᶜ .rel γ0 γ1 ]
    lemma-!ᴿ {[-]} {Q = Q} {γ} (mk sp) =
      !ᴿ _ ⟦ ctx Q γ ⟧ᴿᶜ .resp-≈ ([-]₁η (λ {A} → ⟦_⟧ˢ.refl A))
                                 ([-]₁η (λ {A} → ⟦_⟧ˢ.refl A))
      ∘′ !ᴿ-map f
      ∘′ !ᴿ-* (sp here)
      where
      module ⟦_⟧ˢ A = Setoid ⟦ A ⟧ˢ

      f : WRelMor (!ᴿ (Q here) ⟦ γ here ⟧ᴿ) ⟦ ctx Q γ ⟧ᴿᶜ
      f .sem0 = [-]₁ˢ {S = ⟦_⟧ˢ}
      f .sem1 = [-]₁ˢ {S = ⟦_⟧ˢ}
      f .semsem = id
    lemma-!ᴿ {ε} {Q = Q} {γ} sp = !ᴿ-map f ∘ !ᴿ-ℑ
      where
      module Qγ = Setoid ⟦ ctx Q γ ⟧ˢᶜ

      f : WRelMor Iᴿ ⟦ ctx Q γ ⟧ᴿᶜ
      f .sem0 = record { cong = λ _ → Qγ.refl }
      f .sem1 = record { cong = λ _ → Qγ.refl }
      f .semsem = id
    lemma-!ᴿ {s <+> t} {Q = Q} {γ} (mk sp) =
      !ᴿ _ ⟦ ctx Q γ ⟧ᴿᶜ .resp-≈ (++₁η (λ {A} → ⟦_⟧ˢ.refl A))
                                 (++₁η (λ {A} → ⟦_⟧ˢ.refl A))
      ∘′ !ᴿ-map f
      ∘′ !ᴿ-✴
      ∘′ map-✴ (lemma-!ᴿ (mk (sp ∘ ↙)) , lemma-!ᴿ (mk (sp ∘ ↘)))
      where
      open module ⟦_⟧ˢ A = Setoid ⟦ A ⟧ˢ

      f : WRelMor (⟦ _ ⟧ᴿᶜ ⊗ᴿ ⟦ _ ⟧ᴿᶜ) ⟦ ctx Q γ ⟧ᴿᶜ
      f .sem0 = ++₁ˢ {S = ⟦_⟧ˢ}
      f .sem1 = ++₁ˢ {S = ⟦_⟧ˢ}
      f .semsem = id

    ◇-alg : ∀ {A} (R : WRel _≤_ A) {x y} → ∀[ ◇ (R .rel x y) ⇒ R .rel x y ]
    ◇-alg R (◇⟨ sub ⟩ xy) = R .subres sub xy

    ⟦Tm⟧ᴿ : Scoped 0ℓ
    ⟦Tm⟧ᴿ Rγ A = WRelMor ⟦ Rγ ⟧ᴿᶜ ⟦ A ⟧ᴿ

    wrel : Semantics AnnArr _∋_ ⟦Tm⟧ᴿ
    wrel .ren^𝓥 = ren^∋
    wrel .var v .sem0 = setoid .var v
    wrel .var v .sem1 = setoid .var v
    wrel .var v .semsem = go v
      where
      -- η-expand Rγ to satisfy termination checker (s gets smaller).
      go : ∀ {A s R γ} (let Rγ = ctx {s} R γ) (v : Rγ ∋ A) →
           ∀[ ⟦Tm⟧-rel A Rγ (setoid .var v) (setoid .var v) ]
      go (lvar here ≡.refl (mk le)) = !ᴿ-1 (le here)
      go {γ = γ} (lvar (↙ i) ≡.refl (mk le)) = ◇-alg ⟦ γ (↙ i) ⟧ᴿ ∘′ ✴-1→ ∘′
        map-✴ (go (lvar i ≡.refl (mk (le ∘ ↙))) , lemma-ℑ (mk (le ∘ ↘)))
      go {γ = γ} (lvar (↘ i) ≡.refl (mk le)) = ◇-alg ⟦ γ (↘ i) ⟧ᴿ ∘′ 1-✴→ ∘′
        map-✴ (lemma-ℑ (mk (le ∘ ↙)) , go (lvar i ≡.refl (mk (le ∘ ↘))))
    wrel .alg mm .sem0 = setoid .alg (map-s′ AnnArr (mapK𝓒 sem0) mm)
    wrel .alg mm .sem1 = setoid .alg (map-s′ AnnArr (mapK𝓒 sem1) mm)
    wrel .alg {ctx R γ} (`lam (r , A) B , ≡.refl , mm)
      .semsem γγ .app✴ sp xx =
      mm .get _ .app✴ _ _ .semsem
        (⟦⊴⟧ᴿᶜ {P = R} (mk (λ i → ⊴-trans (+.identity-→ .proj₂ _)
                                          (+-mono ⊴-refl (≤-annihil .proj₂ _))))
               γγ
         ✴⟨ sp ⟩
         !ᴿ-⊴ (⊴-trans (*.identity .proj₂ _) (+.identity-← .proj₁ _)) xx)
    wrel .alg (`app rA B , ≡.refl , mm ✴⟨ sp+ ⟩ (⟨ sp* ⟩· nn)) .semsem γγ =
      let γγ ✴⟨ ⟦sp+⟧ ⟩ rQγγ = lemma-✴ sp+ γγ in
      mm .get _ .app✴ _ _ .semsem γγ .app✴ ⟦sp+⟧
        (!ᴿ-map
          (nn .get _ .app✴ (mk λ i → +.identity-→ .proj₂ _) ([]ᵉ ℑ⟨ 0*-triv ⟩))
          (lemma-!ᴿ sp* rQγγ))
