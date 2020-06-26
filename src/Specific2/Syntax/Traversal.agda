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

  record Hom {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
    constructor mk
    field hom : A → B
    _↦_ : REL A B _
    x ↦ y = hom x ≡ y
    _↤_ : REL B A _
    y ↤ x = y ≡ hom x
  open Hom {{...}} public

  instance
    AnnHom : Hom Dom.Ann Cod.Ann
    AnnHom .hom = apply

    ×Hom : ∀ {a a′ b b′} {A : Set a} {A′ : Set a′} {B : Set b} {B′ : Set b′} →
           {{Hom A B}} → {{Hom A′ B′}} → Hom (A × A′) (B × B′)
    ×Hom .hom = map hom hom

    TyHom : Hom Dom.Ty Cod.Ty
    TyHom .hom = go
      where
      go : Dom.Ty → Cod.Ty
      go tι = tι
      go tI = tI
      go t⊤ = t⊤
      go t0 = t0
      go ((r , A) t⊸ B) = (hom r , go A) t⊸ go B
      go ((p , A) t⊗ (q , B)) = (hom p , go A) t⊗ (hom q , go B)
      go ((p , A) t⊕ (q , B)) = (hom p , go A) t⊕ (hom q , go B)
      go (A t& B) = go A t& go B
      go (t! (r , A)) = t! (hom r , go A)

    VectorHom : ∀ {a b} {A : Set a} {B : Set b} → {{Hom A B}} →
                ∀ {s} → Hom (Vector A s) (Vector B s)
    VectorHom .hom = lift₁ hom

    CtxHom : Hom Dom.Ctx Cod.Ctx
    CtxHom .hom (ctx R Γ) = ctx (hom R) (hom Γ)

    -- SizedCtxHom : ∀ {s} → Hom (Dom.SizedCtx s) (Cod.SizedCtx s)

  hom-⟨_∣ : ∀ {s} (i : Ptr s) → hom Dom.⟨ i ∣ Cod.⊴* Cod.⟨ i ∣
  hom-⟨ i ∣ .get j with does (i ≟ j)
  ... | false = hom-0#
  ... | true = hom-1#

  record Env (T : Cod.Ctx → Cod.Ty → Set) (M : LinMap f t s)
         (Γ : Vector Cod.Ty s) (Δ : Vector Dom.Ty t) : Set where
    open SkewLeftSemimoduleMor M using () renaming (apply to _$M)
    open Dom.IVar
    field act : ∀ {A} → (j : Dom.IVar Δ A)
                      → T (ctx (Dom.1ᴹ (j .idx) $M) Γ) (hom A)
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
      Θ : Vector Dom.Ty u
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
        wk : T PΓ A → T (PΓ ++ᶜ ctx 0* fΘ) A

  module _ {M : LinMap f t s} where
    open SkewLeftSemimoduleMor M
      renaming (apply to infixl 8 _$M; hom-mono to M-mono)
    open Cod
    open SkewLeftSemimodule (Vector-skewLeftSemimodule Cod s)

    obv : ∀ {Q} → Compat M (Q $M) Q
    obv = mk Cod.⊴*-refl

    fixup-0 : Compat M P Q → Q Dom.⊴* Dom.0* → P Cod.⊴* Cod.0*
    fixup-0 (mk com) sp = Cod.⊴*-trans com (Cod.⊴*-trans (M-mono sp) hom-0ₘ)

    fixup-+ : Compat M P Q → Q Dom.⊴* Ql Dom.+* Qr →
              P Cod.⊴* Ql $M Cod.+* Qr $M
    fixup-+ (mk com) sp =
      Cod.⊴*-trans com (Cod.⊴*-trans (M-mono sp) (hom-+ₘ _ _))

    fixup-* : Compat M P Q → Q Dom.⊴* r Dom.*ₗ Q′ →
              P Cod.⊴* hom r Cod.*ₗ Q′ $M
    fixup-* (mk com) sp =
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

  bindCompat : Lift₂ _↤_ fR R →
               Compat M P Q → Compat (bindMap M) (P ++ fR) (Q ++ R)
  bindCompat Rq com .get =
    com .get ++₂ mk λ k → subst (_ Cod.⊴_) (Rq .get k) Cod.⊴-refl
                 -- ⊴*-reflexive

  module _ (K : Kit T) where
    open Kit K

    private
      variable
        A : Dom.Ty
        A′ : Cod.Ty

    open SkewLeftSemimoduleMor

    module _ {M : LinMap f t s} where

      bindEnv : Lift₂ _↤_ fΘ Θ →
                Env T M Γ Δ → Env T (bindMap M) (Γ ++ fΘ) (Δ ++ Θ)
      bindEnv Θq ρ .act (ivar! (↙ j)) = psh
        (Cod.⊴*-refl ++₂ (mk λ k → hom-0#))
        (wk (ρ .act (ivar! j)))
      bindEnv Θq ρ .act (ivar! (↘ k)) =
        vr (lvar (↘ k) (Θq .get k) (M .hom-0ₘ ++₂ hom-⟨ k ∣))

    trav : Env T M Γ Δ → Compat M P Q →
           Dom.Tm (ctx Q Δ) A → Cod.Tm (ctx P Γ) (hom A)
    trav {M = M} ρ (mk com) (var (lvar! j sp)) =
      tm (psh (Cod.⊴*-trans com (M .hom-mono sp)) (ρ .act (ivar! j)))
    trav {M = M} ρ com (app s t sp) =
      app (trav ρ obv s) (trav ρ obv t)
          (Cod.⊴*-trans (fixup-+ com sp)
                        (Cod.+*-mono Cod.⊴*-refl (M .hom-*ₘ _ _)))
    trav ρ com (lam s) =
      lam (trav (bindEnv [ refl ]₂ ρ) (bindCompat [ refl ]₂ com) s)
    trav ρ com (unm s t sp) =
      unm (trav ρ obv s) (trav ρ obv t) (fixup-+ com sp)
    trav ρ com (uni sp) = uni (fixup-0 com sp)
    trav {M = M} ρ com (prm s t sp) =
      prm (trav ρ obv s)
          (trav (bindEnv ([ refl ]₂ ++₂ [ refl ]₂) ρ)
                (bindCompat {M = M} ([ refl ]₂ ++₂ [ refl ]₂) obv)
                t)
          (fixup-+ com sp)
    trav {M = M} ρ com (ten s t sp) =
      ten (trav ρ obv s) (trav ρ obv t)
          (Cod.⊴*-trans (fixup-+ com sp)
                        (Cod.+*-mono (M .hom-*ₘ _ _) (M .hom-*ₘ _ _)))
    trav ρ com (exf s sp) = exf (trav ρ obv s) (fixup-+ com sp)
    trav {M = M} ρ com (cse s t u sp) =
      cse (trav ρ obv s)
          (trav (bindEnv [ refl ]₂ ρ) (bindCompat {M = M} [ refl ]₂ obv) t)
          (trav (bindEnv [ refl ]₂ ρ) (bindCompat {M = M} [ refl ]₂ obv) u)
          (fixup-+ com sp)
    trav ρ com (inl s sp) = inl (trav ρ obv s) (fixup-* com sp)
    trav ρ com (inr s sp) = inr (trav ρ obv s) (fixup-* com sp)
    trav ρ com top = top
    trav ρ com (prl s) = prl (trav ρ com s)
    trav ρ com (prr s) = prr (trav ρ com s)
    trav ρ com (wth s t) = wth (trav ρ com s) (trav ρ com t)
    trav {M = M} ρ com (bam s t sp) =
      bam (trav ρ obv s)
          (trav (bindEnv [ refl ]₂ ρ) (bindCompat {M = M} [ refl ]₂ obv) t)
          (fixup-+ com sp)
    trav ρ com (bng s sp) = bng (trav ρ obv s) (fixup-* com sp)
