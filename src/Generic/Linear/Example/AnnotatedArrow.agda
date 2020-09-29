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

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.Product
  open import Data.Unit
  open import Function.Base using (id; _∘_)
  open import Size
  open import Relation.Unary
  open import Relation.Unary.Bunched
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

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

  module WithStuff
    {W : Set} (Baseᴿ : WRel W Base)
    (_≤0 : W → Set) (_≤[_+_] : W → W → W → Set) (_≤[_*ₗ_] : W → Ann → W → Set)
    where

    open BunchedUnit _≤0
    open BunchedConjunction _≤[_+_]
    open BunchedScaling _≤[_*ₗ_]

    ⟦_⟧ᴿ : ∀ A → WRel W ⟦ A ⟧
    ⟦ base ⟧ᴿ = Baseᴿ
    ⟦ (r , A) ⊸ B ⟧ᴿ f g =
      ⋂ (_ × _) \ (x , y) → (r · ⟦ A ⟧ᴿ x y) ─✴ ⟦ B ⟧ᴿ (f x) (g y)

    ⟦_⟧ᴿᶜ : ∀ RΓ → WRel W ⟦ RΓ ⟧ᶜ
    ⟦ ctx R Γ ⟧ᴿᶜ = go R Γ
      where
      go : ∀ {s} (R : Vector Ann s) (Γ : Vector Ty s) (γ δ : ⟦ ctx R Γ ⟧ᶜ) →
           W → Set
      go {[-]} R Γ γ δ = R here · ⟦ Γ here ⟧ᴿ (γ .get here) (δ .get here)
      go {ε} R Γ γ δ = ✴1
      go {s <+> t} R Γ γ δ =
        go (R ∘ ↙) (Γ ∘ ↙) (mk (γ .get ∘ ↙)) (mk (δ .get ∘ ↙)) ✴
        go (R ∘ ↘) (Γ ∘ ↘) (mk (γ .get ∘ ↘)) (mk (δ .get ∘ ↘))

    ⟦Tm⟧ᴿ : (A : Ty) (RΓ : Ctx) → WRel W (⟦Tm⟧ A RΓ)
    ⟦Tm⟧ᴿ A RΓ m n = ⋂ (_ × _) \ (γ , δ) → ⟦ RΓ ⟧ᴿᶜ γ δ ─✴ ⟦ A ⟧ᴿ (m γ) (n δ)

    record ⟦Tm⟧ᴿ′ (A : Ty) (RΓ : Ctx) : Set where
      field
        m n : ⟦Tm⟧ A RΓ
        w : W
        r : ⟦Tm⟧ᴿ A RΓ m n w

    wrel : Semantics AnnArr LVar ⟦Tm⟧ᴿ′
    wrel .th^𝓥 = th^LVar
    wrel .var v .⟦Tm⟧ᴿ′.m = set .var v
    wrel .var v .⟦Tm⟧ᴿ′.n = set .var v
    wrel .var v .⟦Tm⟧ᴿ′.w = {!!}
    wrel .var v .⟦Tm⟧ᴿ′.r (γ , δ) .app✴ sp γδ = {!!}
    wrel .alg = {!!}
