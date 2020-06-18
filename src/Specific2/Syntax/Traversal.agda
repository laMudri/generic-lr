{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ)

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
  open import Generic.Linear.Syntax as Gen using (ctx)

  open import Algebra.Skew.Construct.Vector
  open import Data.Bool.Base using (Bool; true; false; if_then_else_)
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix using (lift₁ᴹ; Lift₂ᴹ; get)
  open import Data.Product
  open import Function.Base
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

  hom-⟨_∣ : ∀ {s} (i : Ptr s) → lift₁ apply Dom.⟨ i ∣ Cod.⊴* Cod.⟨ i ∣
  hom-⟨ i ∣ .get j with does (i ≟ j)
  ... | false = hom-0#
  ... | true = hom-1#

  hom-ty : Dom.Ty → Cod.Ty
  hom-ann×ty : Dom.Ann × Dom.Ty → Cod.Ann × Cod.Ty
  hom-ty tι = tι
  hom-ty tI = tI
  hom-ty t⊤ = t⊤
  hom-ty t0 = t0
  hom-ty (rA t⊸ B) = hom-ann×ty rA t⊸ hom-ty B
  hom-ty (pA t⊗ qB) = hom-ann×ty pA t⊗ hom-ann×ty qB
  hom-ty (pA t⊕ qB) = hom-ann×ty pA t⊕ hom-ann×ty qB
  hom-ty (A t& B) = hom-ty A t& hom-ty B
  hom-ty (t! rA) = t! (hom-ann×ty rA)
  hom-ann×ty (r , A) = apply r , hom-ty A

  hom-ctx : Dom.Ctx → Cod.Ctx
  hom-ctx (ctx R Γ) = ctx (lift₁ apply R) (lift₁ hom-ty Γ)

  record Env (T : Cod.Ctx → Cod.Ty → Set) (M : LinMap f t s)
         (Γ : Vector Cod.Ty s) (Δ : Vector Dom.Ty t) : Set where
    open SkewLeftSemimoduleMor M using () renaming (apply to _$M)
    open Dom.IVar
    field act : ∀ {A} →
            (j : Dom.IVar Δ A) → T (ctx (Dom.1ᴹ (j .idx) $M) Γ) (hom-ty A)
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

    obv : ∀ {Q} → Compat M (Q $M) Q
    obv = mk Cod.⊴*-refl

    fixup-0 : Compat M P Q → Q Dom.⊴* Dom.0* → P Cod.⊴* Cod.0*
    fixup-0 (mk com) sp = Cod.⊴*-trans com (Cod.⊴*-trans (M-mono sp) hom-0ₘ)

    fixup-+ : Compat M P Q → Q Dom.⊴* Ql Dom.+* Qr →
              P Cod.⊴* Ql $M Cod.+* Qr $M
    fixup-+ (mk com) sp =
      Cod.⊴*-trans com (Cod.⊴*-trans (M-mono sp) (hom-+ₘ _ _))

    fixup-* : Compat M P Q → Q Dom.⊴* r Dom.*ₗ Q′ →
              P Cod.⊴* apply r Cod.*ₗ Q′ $M
    fixup-* (mk com) sp =
      Cod.⊴*-trans com (Cod.⊴*-trans (M-mono sp) (hom-*ₘ _ _))

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

  bindCompat : (∀ k → fR k ≡ apply (R k)) →
               Compat M P Q → Compat (bindMap M) (P ++ fR) (Q ++ R)
  bindCompat q com .get =
    com .get ++₂ mk λ k → subst (_ Cod.⊴_) (q k) Cod.⊴-refl

  module _ (K : Kit T) where
    open Kit K

    private
      variable
        A : Dom.Ty

    open SkewLeftSemimoduleMor

    module _ {M : LinMap f t s} where

      bindEnv : (∀ k → fΘ k ≡ hom-ty (Θ k)) →
                Env T M Γ Δ → Env T (bindMap M) (Γ ++ fΘ) (Δ ++ Θ)
      bindEnv q ρ .act (ivar! (↙ j)) = psh
        (Cod.⊴*-refl ++₂ mk λ k → hom-0#)
        (wk (ρ .act (ivar! j)))
      bindEnv q ρ .act (ivar! (↘ k)) =
        vr (lvar (↘ k) (q k) (M .hom-0ₘ ++₂ hom-⟨ k ∣))

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
