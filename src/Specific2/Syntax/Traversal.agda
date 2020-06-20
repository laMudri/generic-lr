{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ; _⊔_)

module Specific2.Syntax.Traversal
  {Dom Cod : SkewSemiring 0ℓ 0ℓ} (f : SkewSemiringMor Dom Cod) where

  private
    open module f = SkewSemiringMor f
  import Specific2.Syntax.Prelude as Pre
  open import Specific2.Syntax as Syn
    using (tι; tI; t⊤; t0; _t⊸_; _t⊗_; _t⊕_; _t&_; t!
          ; ivar; ivar!; lvar; lvar!
          ; var; app; lam; unm; uni; prm; ten
          ; exf; cse; inl; inr; top; prl; prr; wth; bam; bng)
  open import Generic.Linear.Syntax as Gen using (ctx; sctx)

  open import Algebra.Skew.Construct.Vector
  open import Data.Bool.Base using (Bool; true; false; if_then_else_)
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix using (lift₁ᴹ; Lift₂ᴹ; get)
  open import Data.Product
  open import Data.Product.Relation.Binary.Pointwise.NonDependent
  open import Function.Base
  open import Relation.Binary using (REL)
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary using (Dec; does; proof)

  private
    module Dom where
      open Pre Dom public
      open Syn Ann _⊴_ 0# _+_ 1# _*_ public
      open Gen Ty Ann public hiding (ctx→sctx)

    module Cod where
      open Pre Cod public
      open Syn Ann _⊴_ 0# _+_ 1# _*_ public
      open Gen Ty Ann public hiding (ctx→sctx)

  private
    variable
      s t u : LTree
      T : Cod.Ctx → Cod.Ty → Set
      M : LinMap f t s

  infix 4 _Ty↦_

  record MapsTo (A B : Set) : Set₁ where
    constructor mk
    infix 4 _↦_
    field
      _↦_ : REL A B 0ℓ

  record TotalMapsTo {A B : Set} (mt : MapsTo A B) : Set where
    constructor mk
    open MapsTo mt
    field
      total : ∀ a → ∃ \ b → a ↦ b

  record FunctionalMapsTo {A B : Set} (mt : MapsTo A B) : Set where
    constructor mk
    open MapsTo mt
    field
      func : ∀ a → ∃! _≡_ \ b → a ↦ b

  open MapsTo {{...}} public
  open TotalMapsTo {{...}} public
  open FunctionalMapsTo {{...}} public

  instance
    AnnMapsTo : MapsTo Dom.Ann Cod.Ann
    AnnMapsTo ._↦_ r s = apply r ≡ s

    AnnTotal : TotalMapsTo AnnMapsTo
    AnnTotal .total r = apply r , refl

    AnnFunctional : FunctionalMapsTo AnnMapsTo
    AnnFunctional .func r = apply r , refl , id

    ×MapsTo : ∀ {A A′ B B′ : Set} →
              {{MapsTo A A′}} → {{MapsTo B B′}} → MapsTo (A × B) (A′ × B′)
    ×MapsTo {{mk R}} {{mk S}} = mk (λ (x , y) (x′ , y′) → R x x′ × S y y′)

    ×Total : ∀ {A A′ B B′ : Set} {{ma : MapsTo A A′}} {{mb : MapsTo B B′}} →
             {{TotalMapsTo ma}} → {{TotalMapsTo mb}} →
             TotalMapsTo (×MapsTo {{ma}} {{mb}})
    ×Total {{ma}} {{mb}} {{mk ta}} {{mk tb}} =
      mk λ (x , x′) → let y , p = ta x; y′ , p′ = tb x′ in
                      (y , y′) , (p , p′)

    ×Functional : ∀ {A A′ B B′ : Set}
                    {{ma : MapsTo A A′}} {{mb : MapsTo B B′}} →
                  {{FunctionalMapsTo ma}} → {{FunctionalMapsTo mb}} →
                  FunctionalMapsTo (×MapsTo {{ma}} {{mb}})
    ×Functional {{ma}} {{mb}} {{mk fa}} {{mk fb}} = mk λ (x , x′) →
      let y , e , u = fa x; y′ , e′ , u′ = fb x′ in
      (y , y′) , (e , e′) , (λ (m , m′) → cong₂ _,_ (u m) (u′ m′))

  data _Ty↦_ : REL Dom.Ty Cod.Ty 0ℓ

  instance
    TyMapsTo : MapsTo Dom.Ty Cod.Ty
    TyMapsTo ._↦_ = _Ty↦_

  data _Ty↦_ where
    tι : tι Ty↦ tι
    tI : tI Ty↦ tI
    t0 : t0 Ty↦ t0
    t⊤ : t⊤ Ty↦ t⊤
    _t⊸_ : ∀ {rA rA′ B B′} → rA ↦ rA′ → B ↦ B′ → rA t⊸ B Ty↦ rA′ t⊸ B′
    _t⊗_ : ∀ {pA pA′ qB qB′} → pA ↦ pA′ → qB ↦ qB′ → pA t⊗ qB Ty↦ pA′ t⊗ qB′
    _t⊕_ : ∀ {pA pA′ qB qB′} → pA ↦ pA′ → qB ↦ qB′ → pA t⊕ qB Ty↦ pA′ t⊕ qB′
    _t&_ : ∀ {A A′ B B′} → A ↦ A′ → B ↦ B′ → A t& B Ty↦ A′ t& B′
    t! : ∀ {rA rA′} → rA ↦ rA′ → t! rA Ty↦ t! rA′

  instance
    TyTotal : TotalMapsTo TyMapsTo
    TyTotal = mk go
      where
      go : ∀ A → ∃ \ A′ → A Ty↦ A′
      go× : ∀ rA → ∃ \ rA′ → let mk _↦_ = ×MapsTo {{AnnMapsTo}} {{TyMapsTo}} in
                             rA ↦ rA′

      go tι = tι , tι
      go tI = tI , tI
      go t⊤ = t⊤ , t⊤
      go t0 = t0 , t0
      go (rA t⊸ B) = zip _t⊸_ _t⊸_ (go× rA) (go B)
      go (pA t⊗ qB) = zip _t⊗_ _t⊗_ (go× pA) (go× qB)
      go (pA t⊕ qB) = zip _t⊕_ _t⊕_ (go× pA) (go× qB)
      go (A t& B) = zip _t&_ _t&_ (go A) (go B)
      go (t! rA) = map t! t! (go× rA)

      go× (r , A) = let r′ , rp = total r; A′ , Ap = go A in
                    (r′ , A′) , (rp , Ap)

  instance
    VectorMapsTo : ∀ {A B s} → {{MapsTo A B}} →
                   MapsTo (Vector A s) (Vector B s)
    VectorMapsTo ._↦_ = Lift₂ _↦_

    VectorTotal : ∀ {A B s} {{mt : MapsTo A B}} → {{TotalMapsTo mt}} →
                  TotalMapsTo (VectorMapsTo {A} {B} {s} {{mt}})
    VectorTotal .total v =
      (λ i → total (v i) .proj₁) , (mk λ i → total (v i) .proj₂)

    VectorFunctional :
      ∀ {A B s} {{mt : MapsTo A B}} → {{FunctionalMapsTo mt}} →
      FunctionalMapsTo (VectorMapsTo {A} {B} {s} {{mt}})
    VectorFunctional .func v =
      (λ i → func (v i) .proj₁) , (mk λ i → func (v i) .proj₂ .proj₁)
        , {!λ vv → ?!}

    SizedCtxMapsTo : ∀ {s} → MapsTo (Dom.SizedCtx s) (Cod.SizedCtx s)
    SizedCtxMapsTo ._↦_ (sctx P Γ) (sctx Q Δ) = P ↦ Q × Γ ↦ Δ

    SizedCtxTotal : ∀ {s} → TotalMapsTo (SizedCtxMapsTo {s})
    SizedCtxTotal .total (sctx P Γ) = zip sctx _,_ (total P) (total Γ)

    CtxMapsTo : MapsTo Dom.Ctx Cod.Ctx
    CtxMapsTo ._↦_ (ctx {s} P Γ) (ctx {t} Q Δ) =
      Σ (s ≡ t) \ { refl → sctx P Γ ↦ sctx Q Δ }

    CtxTotal : TotalMapsTo CtxMapsTo
    CtxTotal .total (ctx {s} P Γ) =
      let PΓ′ , PΓp = total (sctx P Γ) in
      Cod.sctx→ctx PΓ′ , (refl , PΓp)

  hom-⟨_∣ : ∀ {s} (i : Ptr s) → lift₁ apply Dom.⟨ i ∣ Cod.⊴* Cod.⟨ i ∣
  hom-⟨ i ∣ .get j with does (i ≟ j)
  ... | false = hom-0#
  ... | true = hom-1#

  record Env (T : Cod.Ctx → Cod.Ty → Set) (M : LinMap f t s)
         (Γ : Vector Cod.Ty s) (Δ : Vector Dom.Ty t) : Set where
    open SkewLeftSemimoduleMor M using () renaming (apply to _$M)
    open Dom.IVar
    field act : ∀ {A A′} → A ↦ A′ →
            (j : Dom.IVar Δ A) → T (ctx (Dom.1ᴹ (j .idx) $M) Γ) A′
  open Env public

  record Compat (M : LinMap f t s) P Q : Set where
    constructor mk
    open SkewLeftSemimoduleMor M using () renaming (apply to _$M)
    field get : P Cod.⊴* (Q $M)
  open Compat public

  record DeployedEnv
    (T : Cod.Ctx → Cod.Ty → Set) (PΓ : Cod.Ctx) (QΔ : Dom.Ctx) : Set
    where
    open Cod.Ctx PΓ renaming (s to γ; Γ to Γ; R to P)
    open Dom.Ctx QΔ renaming (s to δ; Γ to Δ; R to Q)
    field
      linMap : LinMap f δ γ
      env : Env T linMap Γ Δ
      compat : Compat linMap P Q
  open DeployedEnv public

  private
    variable
      r : Dom.Ann
      r′ : Cod.Ann
      P P′ Pl Pr : Vector Cod.Ann s
      Q Q′ Ql Qr : Vector Dom.Ann t
      R : Vector _ u
      fR : Vector Cod.Ann u
      Γ : Vector Cod.Ty s
      Δ : Vector Dom.Ty t
      Θ : Vector _ u
      fΘ : Vector Cod.Ty u

  module _ where

    open Cod hiding (ctx)

    private
      variable
        A : Ty
        PΓ : Ctx

    record Kit (T : Ctx → Ty → Set) : Set where
      field
        psh : P ⊴* P′ → T (ctx P′ Γ) A → T (ctx P Γ) A
        vr : LVar PΓ A → T PΓ A
        tm : T PΓ A → Tm PΓ A
        wk : T PΓ A → T (PΓ ++ᶜ ctx 0* Θ) A

  module _ {M : LinMap f t s} where
    open SkewLeftSemimoduleMor M
      renaming (apply to infixl 8 _$M; hom-mono to M-mono)
    open Cod
    open SkewLeftSemimodule (Vector-skewLeftSemimodule Cod s)

    obv : ∀ {Q} → Compat M (Q $M) Q
    obv = mk Cod.⊴*-refl

    {-
    fixup-0 : Compat M P Q → Q Dom.⊴* Dom.0* → P Cod.⊴* Cod.0*
    fixup-0 (mk com) sp = Cod.⊴*-trans com (Cod.⊴*-trans (M-mono sp) hom-0ₘ)

    fixup-+ : Compat M P Q → Q Dom.⊴* Ql Dom.+* Qr →
              P Cod.⊴* Ql $M Cod.+* Qr $M
    fixup-+ (mk com) sp =
      Cod.⊴*-trans com (Cod.⊴*-trans (M-mono sp) (hom-+ₘ _ _))
    -}

    fixup-* : Compat M P Q → r ↦ r′ → Q Dom.⊴* r Dom.*ₗ Q′ →
              P Cod.⊴* r′ Cod.*ₗ Q′ $M
    fixup-* (mk com) refl sp =
      ⊴*-trans com (⊴*-trans (M-mono sp) (hom-*ₘ _ _))

  module _ where
    open SkewLeftSemimoduleMor
    open ProsetMor

    bindMap : LinMap f t s → LinMap f (t <+> u) (s <+> u)
    bindMap M .prosetMor .apply v = M .apply (v ∘ ↙) ++ lift₁ f.apply (v ∘ ↘)
    bindMap M .prosetMor .hom-mono (mk vv) =
      M .hom-mono (mk (vv ∘ ↙)) ++₂ mk (f.hom-mono ∘ vv ∘ ↘)
    bindMap M .hom-0ₘ = M .hom-0ₘ ++₂ mk λ k → hom-0#
    bindMap M .hom-+ₘ u v =
      M .hom-+ₘ (u ∘ ↙) (v ∘ ↙) ++₂ mk λ k → hom-+ (u (↘ k)) (v (↘ k))
    bindMap M .hom-*ₘ r v =
      M .hom-*ₘ r (v ∘ ↙) ++₂ mk λ k → hom-* r (v (↘ k))

  bindCompat : R ↦ fR → Compat M P Q → Compat (bindMap M) (P ++ fR) (Q ++ R)
  bindCompat RR com .get =
    com .get ++₂ mk λ k → subst (Cod._⊴ _) (RR .get k) Cod.⊴-refl

  module _ (K : Kit T) where
    open Kit K

    private
      variable
        A : Dom.Ty
        A′ : Cod.Ty

    open SkewLeftSemimoduleMor

    module _ {M : LinMap f t s} where

      bindEnv : Θ ↦ fΘ → Env T M Γ Δ → Env T (bindMap M) (Γ ++ fΘ) (Δ ++ Θ)
      bindEnv ΘΘ ρ .act AA (ivar! (↙ j)) = psh
        (Cod.⊴*-refl ++₂ mk λ k → hom-0#)
        (wk (ρ .act AA (ivar! j)))
      bindEnv ΘΘ ρ .act AA (ivar! (↘ k)) =
        vr (lvar (↘ k) {!ΘΘ .get k!} (M .hom-0ₘ ++₂ hom-⟨ k ∣))
        -- vr (lvar (↘ k) (q k) (M .hom-0ₘ ++₂ hom-⟨ k ∣))

    trav : Env T M Γ Δ → Compat M P Q → A ↦ A′ →
           Dom.Tm (ctx Q Δ) A → Cod.Tm (ctx P Γ) A′
    trav ρ com AA (var x) = {!!}
    trav ρ com AA (app s t sp) = {!!}
    trav {M = M} ρ com ((rr , AA) t⊸ BB) (lam s) =
      lam (trav (bindEnv {M = M} [ AA ]₂ ρ) (bindCompat [ rr ]₂ com) BB s)
    trav ρ com AA (unm s t sp) = {!!}
    trav ρ com AA (uni sp) = {!!}
    trav ρ com AA (prm s t sp) = {!!}
    trav ρ com AA (ten s t sp) = {!!}
    trav ρ com AA (exf s sp) = {!!}
    trav ρ com AA (cse s t u sp) = {!!}
    trav {M = M} ρ com ((pp , AA) t⊕ _) (inl s sp) =
      inl (trav ρ (obv {M = M}) AA s) (fixup-* com pp sp)
    trav ρ com AA (inr s sp) = {!!}
    trav ρ com t⊤ top = top
    trav ρ com AA (prl s) = prl (trav ρ com (AA t& total _ .proj₂) s)
    trav ρ com AA (prr s) = {!!}
    trav ρ com (AA t& BB) (wth s t) = wth (trav ρ com AA s) (trav ρ com BB t)
    trav ρ com AA (bam s t sp) = {!!}
    trav ρ com AA (bng s sp) = {!!}

  {-
  module _ (K : Kit T) where
    open Kit K

    private
      variable
        A : Dom.Ty

    open SkewLeftSemimoduleMor

    trav : Env T M Γ Δ → Compat M P Q →
           Dom.Tm (ctx Q Δ) A → Cod.Tm (ctx P Γ) (hom-ty A)
    trav {M = M} ρ (mk com) (var (lvar! j sp)) =
      tm (psh (Cod.⊴*-trans com (M .hom-mono sp)) (ρ .act (ivar! j)))
    trav {M = M} ρ com (app s t sp) =
      app (trav ρ obv s) (trav ρ obv t)
          (Cod.⊴*-trans (fixup-+ com sp)
                        (Cod.+*-mono Cod.⊴*-refl (M .hom-*ₘ _ _)))
    trav ρ com (lam s) =
      lam (trav (bindEnv (λ- refl) ρ) (bindCompat (λ- refl) com) s)
    trav ρ com (unm s t sp) =
      unm (trav ρ obv s) (trav ρ obv t) (fixup-+ com sp)
    trav ρ com (uni sp) = uni (fixup-0 com sp)
    trav {M = M} ρ com (prm s t sp) =
      prm (trav ρ obv s)
          (trav (bindEnv (λ { (↙ k) → refl ; (↘ k) → refl }) ρ)
                (bindCompat {M = M} (λ { (↙ k) → refl ; (↘ k) → refl }) obv)
                t)
          (fixup-+ com sp)
    trav {M = M} ρ com (ten s t sp) =
      ten (trav ρ obv s) (trav ρ obv t)
          (Cod.⊴*-trans (fixup-+ com sp)
                        (Cod.+*-mono (M .hom-*ₘ _ _) (M .hom-*ₘ _ _)))
    trav ρ com (exf s sp) = exf (trav ρ obv s) (fixup-+ com sp)
    trav {M = M} ρ com (cse s t u sp) =
      cse (trav ρ obv s)
          (trav (bindEnv (λ- refl) ρ) (bindCompat {M = M} (λ- refl) obv) t)
          (trav (bindEnv (λ- refl) ρ) (bindCompat {M = M} (λ- refl) obv) u)
          (fixup-+ com sp)
    trav ρ com (inl s sp) = inl (trav ρ obv s) (fixup-* com sp)
    trav ρ com (inr s sp) = inr (trav ρ obv s) (fixup-* com sp)
    trav ρ com top = top
    trav ρ com (prl s) = prl (trav ρ com s)
    trav ρ com (prr s) = prr (trav ρ com s)
    trav ρ com (wth s t) = wth (trav ρ com s) (trav ρ com t)
    trav {M = M} ρ com (bam s t sp) =
      bam (trav ρ obv s)
          (trav (bindEnv (λ- refl) ρ) (bindCompat {M = M} (λ- refl) obv) t)
          (fixup-+ com sp)
    trav ρ com (bng s sp) = bng (trav ρ obv s) (fixup-* com sp)
  -}
