{-# OPTIONS --safe --sized-types --without-K --prop --postfix-projections #-}

module Generic.Linear.Example.Translation.LnL-LR where

  open import Algebra.Relational
  open import Algebra.Skew
  open import Data.Hand
  open import Data.LTree
  open import Data.LTree.Vector hiding (++ˢ)
  open import Data.LTree.Matrix
  open import Data.LTree.Automation
  open import Data.Product
  open import Data.Sum
  open import Data.Unit
  open import Data.Wrap
  open import Function
  open import Function.Equality
  open import Function.Equivalence
  open import Level
  open import Proposition
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)
  open import Relation.Unary
  open import Relation.Unary.Bunched
  open import Size

  open import Generic.Linear.Example.LLFlags
  open import Generic.Linear.Example.ZeroOneMany renaming (u01ω to Ann)
  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Algebra skewSemiring

  open import Generic.Linear.Example.LR
  module LR where
    open WithLLFlags (record noLLFlags
      { Has-I = ⊤ᴾ; Has-⊗ = ⊤ᴾ; Has-⊸ = ⊤ᴾ; Has-! = ⊤ᴾ })
      public hiding (var)
    open import Generic.Linear.Environment Ty rawSkewSemiring public
    open import Generic.Linear.Environment.Properties Ty skewSemiring public
    open import Generic.Linear.Thinning.Properties Ty skewSemiring public
    open import Generic.Linear.Thinning.Monoidal Ty skewSemiring public
    open import Generic.Linear.Extend Ty skewSemiring public
    open import Generic.Linear.Semantics Ty skewSemiring public
    open import Generic.Linear.Semantics.Syntactic Ty skewSemiring public
  open LR using
    ( `LR; LR; ι; tI; _t⊗_; _t⊸_; t!
    ; `Ii; `Ie; `⊗i; `⊗e; `⊸i; `⊸e; `!i; `!e
    )

  module LnL where
    open import Generic.Linear.Example.LnL public
    open import Generic.Linear.Environment ΣTy rawSkewSemiring public
    open import Generic.Linear.Environment.Properties ΣTy skewSemiring public
    open import Generic.Linear.Thinning.Properties ΣTy skewSemiring public
    open import Generic.Linear.Thinning.Monoidal ΣTy skewSemiring public
    open import Generic.Linear.Extend ΣTy skewSemiring public
    open import Generic.Linear.Semantics ΣTy skewSemiring public
    open import Generic.Linear.Semantics.Syntactic ΣTy skewSemiring public
  open LnL using
    ( `LnL; LnL; lin; int; ι; tI; _t⊗_; _t⊸_; tF; t1; _t×_; _t→_; tG
    ; `Ii; `Ie; `⊗i; `⊗e; `⊸i; `⊸e; `Fi; `Fe
    ; `1i; `×i; `×e; `→i; `→e; `Gi; `Ge
    )

  infixl 8 _ᵒTy _*Ty

  _ᵒTy : LR.Ty → LnL.Ty lin
  ι ᵒTy = ι
  tI ᵒTy = tI
  (A t⊗ B) ᵒTy = A ᵒTy t⊗ B ᵒTy
  (A t⊸ B) ᵒTy = A ᵒTy t⊸ B ᵒTy
  t! A ᵒTy = tF (tG (A ᵒTy))

  _*Ty : ∀ {f} → LnL.Ty f → LR.Ty
  ι *Ty = ι
  tI *Ty = tI
  (A t⊗ B) *Ty = A *Ty t⊗ B *Ty
  (A t⊸ B) *Ty = A *Ty t⊸ B *Ty
  (tF X) *Ty = t! (X *Ty)
  t1 *Ty = tI
  (X t× Y) *Ty = t! (X *Ty) t⊗ t! (Y *Ty)
  (X t→ Y) *Ty = t! (X *Ty) t⊸ Y *Ty
  (tG A) *Ty = A *Ty

  _*ΣTy : LnL.ΣTy → LR.Ty
  A *ΣTy = A .proj₂ *Ty

  module _ where
    open LnL.Ctx
    open LR.Ctx

    infixl 8 _ᵒCtx _*Ctx

    _ᵒCtx : LR.Ctx → LnL.Ctx
    (RΓ ᵒCtx) .s = RΓ .s
    (RΓ ᵒCtx) .R = RΓ .R
    (RΓ ᵒCtx) .Γ i = _ , RΓ .Γ i ᵒTy

    _*Ctx : LnL.Ctx → LR.Ctx
    (RΓ *Ctx) .s = RΓ .s
    (RΓ *Ctx) .R = RΓ .R
    (RΓ *Ctx) .Γ i = RΓ .Γ i *ΣTy

  module _ where
    open LnL._─Env
    open LnL.Var
    open LnL.LVar

    o-distrib-[]ᶜ : LnL.Thinning (LR.[]ᶜ ᵒCtx) LnL.[]ᶜ
    o-distrib-[]ᶜ .M = 1ᴹ
    o-distrib-[]ᶜ .sums = []₂
    o-distrib-[]ᶜ .lookup (LnL.var (there () i) q)

    o-distrib-++ᶜ : ∀ {PΓ QΔ} →
      LnL.Thinning ((PΓ LR.++ᶜ QΔ) ᵒCtx) (PΓ ᵒCtx LnL.++ᶜ QΔ ᵒCtx)
    o-distrib-++ᶜ .M = 1ᴹ
    o-distrib-++ᶜ {LR.ctx P Γ} {LR.ctx Q Δ} .sums =
      ⊴*-trans (+*-identity↘ _)
        (+*-mono (unrowL₂ (*ᴹ-1ᴹ (row P))) (unrowL₂ (*ᴹ-0ᴹ (row Q))))
      ++₂
      ⊴*-trans (+*-identity↙ _)
        (+*-mono (unrowL₂ (*ᴹ-0ᴹ (row P))) (unrowL₂ (*ᴹ-1ᴹ (row Q))))
    o-distrib-++ᶜ .lookup v .idx = v .idx
    o-distrib-++ᶜ .lookup v .tyq with v .idx | v .tyq
    ... | ↙ i | q = q
    ... | ↘ i | q = q
    o-distrib-++ᶜ .lookup v .basis = ⊴*-refl

    o𝓒 : LR.Scoped 0ℓ
    o𝓒 A PΓ = LnL.Term (_ , A ᵒTy) (PΓ ᵒCtx)

    oreify : ∀ {RΘ A} →
      ∀[ LR.Kripke LR.LVar o𝓒 RΘ A ⇒
         (λ PΓ → LnL.Term (_ , A ᵒTy) (PΓ ᵒCtx LnL.++ᶜ RΘ ᵒCtx)) ]
    oreify t = LnL.ren o-distrib-++ᶜ (LR.reify t)

  module _ where
    open LR.Semantics
    open LnL._─Env

    oSem : LR.Semantics LR LR.LVar o𝓒
    oSem .th^𝓥 = LR.th^LVar
    oSem .var (LR.lvar i refl b) = LnL.`var (LnL.lvar i refl b)
    oSem .alg (`Ii , refl , ℑ⟨ sp0 ⟩) = LnL.`con (`Ii , refl , ℑ⟨ sp0 ⟩)
    oSem .alg (`Ie Z , refl , s ✴⟨ sp+ ⟩ t) =
      let ths = LnL.1ᵗ LnL.++ᵗ o-distrib-[]ᶜ in
      let tht = LnL.1ᵗ LnL.++ᵗ o-distrib-[]ᶜ in
      LnL.`con (`Ie _ , refl ,
        LnL.ren ths (oreify s) ✴⟨ sp+ ⟩ LnL.ren tht (oreify t))
    oSem .alg (`⊗i A B , refl , s ✴⟨ sp+ ⟩ t) =
      let ths = LnL.1ᵗ LnL.++ᵗ o-distrib-[]ᶜ in
      let tht = LnL.1ᵗ LnL.++ᵗ o-distrib-[]ᶜ in
      LnL.`con (`⊗i _ _ , refl ,
        LnL.ren ths (oreify s) ✴⟨ sp+ ⟩ LnL.ren tht (oreify t))
    oSem .alg (`⊗e A B Z , refl , s ✴⟨ sp+ ⟩ t) =
      let ths = LnL.1ᵗ LnL.++ᵗ o-distrib-[]ᶜ in
      let tht = LnL.1ᵗ LnL.++ᵗ o-distrib-++ᶜ in
      LnL.`con (`⊗e _ _ _ , refl ,
        LnL.ren ths (oreify s) ✴⟨ sp+ ⟩ LnL.ren tht (oreify t))
    oSem .alg (`⊸i A B , refl , t) = LnL.`con (`⊸i _ _ , refl , oreify t)
    oSem .alg (`⊸e A B , refl , s ✴⟨ sp+ ⟩ t) =
      let ths = LnL.1ᵗ LnL.++ᵗ o-distrib-[]ᶜ in
      let tht = LnL.1ᵗ LnL.++ᵗ o-distrib-[]ᶜ in
      LnL.`con (`⊸e _ _ , refl ,
        LnL.ren ths (oreify s) ✴⟨ sp+ ⟩ LnL.ren tht (oreify t))
    oSem .alg (`!i A , refl , ⟨_⟩·_ {R} sp* t) =
      let tht = (th LnL.++ᵗ o-distrib-[]ᶜ) LnL.>>ᵗ LnL.++-[]ᵗ← in
      LnL.`con (`Fi _ , refl ,
        □⟨ sp* , (mk λ i → ω*-del (R i)) , (mk λ i → ω*-dup (R i)) ⟩
          LnL.`con (`Gi _ , refl ,
            □⟨ ⊴*-refl , (mk λ i → ω*-del (R i)) ++₂ []₂
                       , (mk λ i → ω*-dup (R i)) ++₂ []₂ ⟩
              LnL.ren tht (oreify t)))
      where
      th : ∀ {s R Γ} → LnL.Thinning (LnL.ctx {s} R Γ) (LnL.ctx (uω *ₗ R) Γ)
      th .M = 1ᴹ
      th {R = R} .sums =
        ⊴*-trans (mk λ i → ω*-⊴ (R i)) (unrowL₂ (*ᴹ-1ᴹ (row R)))
      th .lookup v = record { LnL.Var v; basis = ⊴*-refl }
    oSem .alg (`!e A Z , refl , s ✴⟨ sp+ ⟩ t) =
      let ths = LnL.1ᵗ LnL.++ᵗ o-distrib-[]ᶜ in
      LnL.`con (`Fe _ _ , refl ,
        LnL.ren ths (oreify s)
          ✴⟨ sp+ ⟩
        LnL.sub (LnL.1ˢ LnL.++ˢ σ) (oreify t))
      where
      σ : ∀ {A} →
        LnL.Substitution LnL (LnL.[ uω · _ , A ]ᶜ) (LnL.[ uω · _ , tG A ]ᶜ)
      σ .M _ _ = uω
      σ .sums .get i = ⊴-refl
      σ .lookup (LnL.var here refl) =
        LnL.`con (`Ge _ , refl , □⟨ ⊴*-refl , [ ω⊴0 ]₂ , ⊴*-refl ⟩
          LnL.`var (LnL.lvar (↙ here) refl ([ ω⊴1 ]₂ ++₂ []₂)))

  _ᵒTm : ∀ {A Γ} → LR.Term A Γ → LnL.Term (_ , A ᵒTy) (Γ ᵒCtx)
  _ᵒTm = LR.Semantics.semantics oSem LR.identity

  module _ where
    open LR._─Env
    open LR.Var
    open LR.LVar

    *-distrib-[]ᶜ : LR.Thinning (LnL.[]ᶜ *Ctx) LR.[]ᶜ
    *-distrib-[]ᶜ .M = 1ᴹ
    *-distrib-[]ᶜ .sums = []₂
    *-distrib-[]ᶜ .lookup (LR.var (there () i) q)

    *-distrib-++ᶜ : ∀ {PΓ QΔ} →
      LR.Thinning ((PΓ LnL.++ᶜ QΔ) *Ctx) (PΓ *Ctx LR.++ᶜ QΔ *Ctx)
    *-distrib-++ᶜ .M = 1ᴹ
    *-distrib-++ᶜ {LnL.ctx P Γ} {LnL.ctx Q Δ} .sums =
      ⊴*-trans (+*-identity↘ _)
        (+*-mono (unrowL₂ (*ᴹ-1ᴹ (row P))) (unrowL₂ (*ᴹ-0ᴹ (row Q))))
      ++₂
      ⊴*-trans (+*-identity↙ _)
        (+*-mono (unrowL₂ (*ᴹ-0ᴹ (row P))) (unrowL₂ (*ᴹ-1ᴹ (row Q))))
    *-distrib-++ᶜ .lookup v .idx = v .idx
    *-distrib-++ᶜ .lookup v .tyq with v .idx | v .tyq
    ... | ↙ i | q = q
    ... | ↘ i | q = q
    *-distrib-++ᶜ .lookup v .basis = ⊴*-refl

  module _ where
    open LnL.Semantics
    open LnL._─Env
    open LR._─Env

    *𝓒 : LnL.Scoped 0ℓ
    *𝓒 A PΓ = LR.Term (A *ΣTy) (PΓ *Ctx)

    *reify : ∀ {RΘ A} →
      ∀[ LnL.Kripke LnL.LVar *𝓒 RΘ A ⇒
         (λ PΓ → LR.Term (A *ΣTy) (PΓ *Ctx LR.++ᶜ RΘ *Ctx)) ]
    *reify t = LR.ren *-distrib-++ᶜ (LnL.reify t)

    *Sem : LnL.Semantics LnL LnL.LVar *𝓒
    *Sem .th^𝓥 = LnL.th^LVar
    *Sem .var (LnL.lvar i q b) = LR.`var (LR.lvar i (≡.cong _*ΣTy q) b)
    *Sem .alg (`Ii , refl , ℑ⟨ sp0 ⟩) = LR.`con (`Ii , refl , ℑ⟨ sp0 ⟩)
    *Sem .alg (`Ie C , refl , s ✴⟨ sp+ ⟩ t) =
      let ths = LR.1ᵗ LR.++ᵗ *-distrib-[]ᶜ in
      let tht = LR.1ᵗ LR.++ᵗ *-distrib-[]ᶜ in
      LR.`con (`Ie _ , refl ,
        LR.ren ths (*reify s) ✴⟨ sp+ ⟩ LR.ren tht (*reify t))
    *Sem .alg (`⊗i A B , refl , s ✴⟨ sp+ ⟩ t) =
      let ths = LR.1ᵗ LR.++ᵗ *-distrib-[]ᶜ in
      let tht = LR.1ᵗ LR.++ᵗ *-distrib-[]ᶜ in
      LR.`con (`⊗i _ _ , refl ,
        LR.ren ths (*reify s) ✴⟨ sp+ ⟩ LR.ren tht (*reify t))
    *Sem .alg (`⊗e A B C , refl , s ✴⟨ sp+ ⟩ t) =
      let ths = LR.1ᵗ LR.++ᵗ *-distrib-[]ᶜ in
      let tht = LR.1ᵗ LR.++ᵗ *-distrib-++ᶜ in
      LR.`con (`⊗e _ _ _ , refl ,
        LR.ren ths (*reify s) ✴⟨ sp+ ⟩ LR.ren tht (*reify t))
    *Sem .alg (`⊸i A B , refl , t) =
      LR.`con (`⊸i _ _ , refl , *reify t)
    *Sem .alg (`⊸e A B , refl , s ✴⟨ sp+ ⟩ t) =
      let ths = LR.1ᵗ LR.++ᵗ *-distrib-[]ᶜ in
      let tht = LR.1ᵗ LR.++ᵗ *-distrib-[]ᶜ in
      LR.`con (`⊸e _ _ , refl ,
        LR.ren ths (*reify s) ✴⟨ sp+ ⟩ LR.ren tht (*reify t))
    *Sem .alg (`Fi X , refl , □⟨ str , sp0 , sp+ ⟩ t) =
      let th = LR.subuse-th str LR.++ᵗ *-distrib-[]ᶜ in
      LR.`con (`!i _ , refl ,
        ⟨ (mk λ i → lemma (⊴-trans (str .get i) (sp0 .get i))) ⟩·
          LR.ren th (*reify t))
      where
      lemma : ∀ {x} → x ⊴ u0 → x ⊴ uω * x
      lemma ⊴-refl = ⊴-refl
      lemma ω⊴0 = ⊴-refl
    *Sem .alg (`Fe X C , refl , s ✴⟨ sp+ ⟩ t) =
      let ths = LR.1ᵗ LR.++ᵗ *-distrib-[]ᶜ in
      LR.`con (`!e _ _ , refl , LR.ren ths (*reify s) ✴⟨ sp+ ⟩ *reify t)
    *Sem .alg (`1i , refl , □⟨ str , sp0 , sp+ ⟩ _) =
      LR.`con (`Ii , refl , ℑ⟨ ⊴*-trans str sp0 ⟩)
    *Sem .alg (`×i X Y , refl , □⟨ str , sp0 , sp+ ⟩ (s , t)) =
      let ths = LR.++-[]ᵗ← LR.++ᵗ *-distrib-[]ᶜ in
      let tht = LR.++-[]ᵗ← LR.++ᵗ *-distrib-[]ᶜ in
      LR.`con (`⊗i _ _ , refl ,
        LR.`con (`!i _ , refl ,
          ⟨ (mk λ i → lemma (sp0 .get i)) ++₂ []₂ ⟩· LR.ren ths (*reify s))
          ✴⟨ ⊴*-trans str sp+ ⟩
        LR.`con (`!i _ , refl ,
          ⟨ (mk λ i → lemma (sp0 .get i)) ++₂ []₂ ⟩· (LR.ren tht (*reify t))))
      where
      lemma : ∀ {x} → x ⊴ u0 → x ⊴ uω * x
      lemma ⊴-refl = ⊴-refl
      lemma ω⊴0 = ⊴-refl
    *Sem .alg (`×e ll X Y , refl , □⟨ str , sp0 , sp+ ⟩ t) =
      let th = LR.1ᵗ LR.++ᵗ *-distrib-[]ᶜ in
      LR.`con (`⊗e _ _ _ , refl ,
        LR.ren th (*reify t)
          ✴⟨ ⊴*-trans str (+*-identity↘ _) ⟩
        LR.`con (`!e _ _ , refl ,
          LR.`var (LR.lvar (↙ (↘ (↙ here))) refl (⊴*-refl ++₂ []₂))
            ✴⟨ ⊴*-refl ++₂ ([ ⊴-refl ]₂ ++₂ [ ⊴-refl ]₂) ⟩
          LR.`con (`!e _ _ , refl ,
            LR.`var (LR.lvar (↙ (↙ (↘ (↘ here)))) refl (⊴*-refl ++₂ []₂))
              ✴⟨ ⊴*-refl ++₂ [ ω⊴1 ]₂ ⟩
            LR.`var (LR.lvar (↙ (↘ here)) refl (⊴*-refl ++₂ [ ω⊴0 ]₂)))))
    *Sem .alg (`×e rr X Y , refl , □⟨ str , sp0 , sp+ ⟩ t) =
      let th = LR.1ᵗ LR.++ᵗ *-distrib-[]ᶜ in
      LR.`con (`⊗e _ _ _ , refl ,
        LR.ren th (*reify t)
          ✴⟨ ⊴*-trans str (+*-identity↘ _) ⟩
        LR.`con (`!e _ _ , refl ,
          LR.`var (LR.lvar (↙ (↘ (↙ here))) refl (⊴*-refl ++₂ []₂))
            ✴⟨ ⊴*-refl ++₂ ([ ⊴-refl ]₂ ++₂ [ ⊴-refl ]₂) ⟩
          LR.`con (`!e _ _ , refl ,
            LR.`var (LR.lvar (↙ (↙ (↘ (↘ here)))) refl (⊴*-refl ++₂ []₂))
              ✴⟨ ⊴*-refl ++₂ [ ω⊴0 ]₂ ⟩
            LR.`var (LR.lvar (↘ here) refl (⊴*-refl ++₂ [ ω⊴1 ]₂)))))
    *Sem .alg (`→i X Y , refl , □⟨ str , sp0 , sp+ ⟩ t) =
      let th = LR.extendʳ LR.++ᵗ LR.1ᵗ in
      LR.`con (`⊸i _ _ , refl ,
        LR.`con (`!e _ _ , refl ,
          LR.`var (LR.lvar (↙ (↘ here)) refl (⊴*-refl ++₂ []₂))
            ✴⟨ str ++₂ [ ⊴-refl ]₂ ⟩
          LR.ren th (*reify t)))
    *Sem .alg (`→e X Y , refl , □⟨ str , sp0 , sp+ ⟩ (s , t)) =
      let ths = LR.1ᵗ LR.++ᵗ *-distrib-[]ᶜ in
      let tht = LR.++-[]ᵗ← LR.++ᵗ *-distrib-[]ᶜ in
      LR.`con (`⊸e _ _ , refl ,
        LR.ren ths (*reify s)
          ✴⟨ ⊴*-trans str sp+ ⟩
        LR.`con (`!i _ , refl , ⟨ (mk λ i → lemma (sp0 .get i)) ++₂ []₂ ⟩·
          LR.ren tht (*reify t)))
      where
      lemma : ∀ {x} → x ⊴ u0 → x ⊴ uω * x
      lemma ⊴-refl = ⊴-refl
      lemma ω⊴0 = ⊴-refl
    *Sem .alg (`Gi A , refl , □⟨ str , sp0 , sp+ ⟩ t) =
      let th = (LR.subuse-th str LR.++ᵗ *-distrib-[]ᶜ) LR.>>ᵗ LR.++-[]ᵗ→ in
      LR.ren th (*reify t)
    *Sem .alg (`Ge A , refl , □⟨ str , sp0 , sp+ ⟩ t) =
      let th = (LR.subuse-th str LR.++ᵗ *-distrib-[]ᶜ) LR.>>ᵗ LR.++-[]ᵗ→ in
      LR.ren th (*reify t)
