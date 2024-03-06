{-# OPTIONS --sized-types --without-K --prop --postfix-projections #-}

module Generic.Linear.Example.Translation.LnL-LR where

  open import Algebra.Relational
  open import Algebra.Po
  open import Data.Bool using (Bool; true; false; if_then_else_)
  open import Data.Bool.Extra
  open import Data.Hand
  open import Data.LTree
  open import Data.LTree.Vector hiding ([]ˢ; ++ˢ)
  open import Data.LTree.Automation
  open import Data.Product
  open import Data.Sum
  open import Data.Unit using (⊤; tt)
  open import Data.Wrap renaming ([_] to mk)
  open import Function as F
  open import Level
  open import Proposition
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)
  open import Relation.Nary
  open import Relation.Nullary using (Dec; yes; no; does; proof; ofʸ; ofⁿ)
  open import Relation.Unary.Bunched
  open import Size

  open import Generic.Linear.Example.LLFlags
  open import Generic.Linear.Example.ZeroOneMany renaming (0#1ω to Ann)
  open import Generic.Linear.Example.ZeroOneMany.LinIntView
  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring

  private
    open module Dummy {s} =
      FRelLeftSemimodule (Vᶠᴿ s) hiding (0ₘ-mono; +ₘ-mono; *ₘ-mono)

  open import Generic.Linear.Example.LR
  module LR where
    open WithLLFlags (record noLLFlags
      { Has-I = ⊤ᴾ; Has-⊗ = ⊤ᴾ; Has-⊸ = ⊤ᴾ; Has-! = ⊤ᴾ })
      public
    open import Generic.Linear.Environment Ty poSemiring public
    open import Generic.Linear.Environment.Properties Ty poSemiring public
    open import Generic.Linear.Environment.Categorical Ty poSemiring public
    open import Generic.Linear.Renaming.Properties Ty poSemiring public
    open import Generic.Linear.Renaming.Monoidal Ty poSemiring public
    open import Generic.Linear.Semantics Ty poSemiring public
    open import Generic.Linear.Semantics.Syntactic Ty poSemiring public
    infix 20 _⇒ˢ_
    _⇒ˢ_ = [ LR ]_⇒ˢ_
  open LR using
    ( `LR; LR; ι; tI; _t⊗_; _t⊸_; t!
    ; `Ii; `Ie; `⊗i; `⊗e; `⊸i; `⊸e; `!i; `!e
    ; ctx; shape; use-ctx; ty-ctx
    )

  module LnL where
    open import Generic.Linear.Example.LnL public
    open import Generic.Linear.Variable ΣTy rawPoSemiring public
    open import Generic.Linear.Environment ΣTy poSemiring public
    open import Generic.Linear.Environment.Properties ΣTy poSemiring public
    open import Generic.Linear.Environment.Categorical ΣTy poSemiring public
    open import Generic.Linear.Renaming.Properties ΣTy poSemiring public
    open import Generic.Linear.Renaming.Monoidal ΣTy poSemiring public
    open import Generic.Linear.Semantics ΣTy poSemiring public
    open import Generic.Linear.Semantics.Syntactic ΣTy poSemiring public
    open import Generic.Linear.Environment.Renameable ΣTy poSemiring Term ren^⊢ public
      using () renaming (pw-env to pw-sub)
    open import Generic.Linear.Example.ZeroOneMany.Proper ΣTy public
    infix 20 _⇒ˢ_
    _⇒ˢ_ = [ LnL ]_⇒ˢ_
  open LnL using
    ( `LnL; LnL; lin; int; ι; tI; _t⊗_; _t⊸_; tF; t1; _t×_; _t→_; tG
    ; `Ii; `Ie; `⊗i; `⊗e; `⊸i; `⊸e; `Fi; `Fe
    ; `1i; `×i; `×e; `→i; `→e; `Gi; `Ge
    ; ctx; shape; use-ctx; ty-ctx
    )

  open WithLLFlags using (ℑᶜ⟨_⟩; _✴ᶜ⟨_⟩_; ⟨_⟩·ᶜ_; □ᶜ⟨_⟩_; mkᶜ)

  infixl 28 _ᵒTy _*Ty _*ΣTy

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

  o-var : Ann → LR.Ty → LnL.ΣTy
  o-var r A = if is-lin r
    then (lin , A ᵒTy)
    else (int , tG (A ᵒTy))

  o-var* : ∀ {s} → Vector Ann s → Vector LR.Ty s → Vector LnL.ΣTy s
  o-var* = lift₂ o-var

  o-ann : Ann → Ann → Ann
  o-ann r s = if is-lin r then s else ω#

  o-ann-≤ : ∀ r s → o-ann r s ≤ s
  o-ann-≤ r s with liview r
  ... | view-int = ω#≤
  ... | view-lin l = ≤-refl

  o-ann* : ∀ {s} → Vector Ann s → Vector Ann s → Vector Ann s
  o-ann* = lift₂ o-ann

  o-ann*-≤ : ∀ {s} (R P : Vector Ann s) → o-ann* R P ≤* P
  o-ann*-≤ R P .get i = o-ann-≤ _ _

  mend-+* : ∀ {s} {R P Q : Vector Ann s} → R ≤[ P +* Q ] →
    R ≤[ o-ann* R P +* o-ann* R Q ]
  mend-+* {R = R} sp+ .get i with {R i} | liview (R i) | sp+ .get i
  ... | view-int | sp+i = ≤-refl
  ... | view-lin l | sp+i = sp+i

  mend-*ₗ : ∀ {s} {R P : Vector Ann s} → R ≤[ ω# *ₗ P ] → R ≤[ ω# *ₗ R ]
  mend-*ₗ {R = R} {P} sp* .get i with R i | sp* .get i
  ... | 0# | sp*i = ≤-refl
  ... | ω# | sp*i = ≤-refl
  ... | 1# | sp*i with P i
  mend-*ₗ sp* .get i | 1# | () | 0#
  ...   | 1# = sp*i
  ...   | ω# = sp*i

  module _ where
    open LnL.Ctx
    open LR.Ctx

    infixl 28 _ᵒCtx _*Ctx

    _ᵒCtx : LR.Ctx → LnL.Ctx
    (Γ ᵒCtx) .shape = Γ .shape
    (Γ ᵒCtx) .use-ctx = Γ .use-ctx
    (Γ ᵒCtx) .ty-ctx = o-var* (Γ .use-ctx) (Γ .ty-ctx)

    _*Ctx : LnL.Ctx → LR.Ctx
    (Γ *Ctx) .shape = Γ .shape
    (Γ *Ctx) .use-ctx = Γ .use-ctx
    (Γ *Ctx) .ty-ctx i = Γ .ty-ctx i *ΣTy

  module _ where
    open LnL.[_]_⇒ᵉ_
    open LnL._∋_

    o-distrib-[]ᶜ : LnL.[]ᶜ LnL.⇒ʳ (LR.[]ᶜ ᵒCtx)
    o-distrib-[]ᶜ = LnL.[]ʳ′

    o-distrib-++ᶜ : ∀ {Γ Δ} →
      Γ ᵒCtx LnL.++ᶜ Δ ᵒCtx LnL.⇒ʳ (Γ LR.++ᶜ Δ) ᵒCtx
    o-distrib-++ᶜ = LnL.1ʳ LnL.++ʳ′ LnL.1ʳ

    open LnL using
      ( _⇒ʳ_; ren; ↙ʳ; ↘ʳ; []ʳ; _++ʳ_; 1ʳ; _>>ʳ_
      ; _⇒ˢ_; sub; []ˢ; _++ˢ_; 1ˢ; _>>ˢ_; ren-to-sub
      )
    open LnL.With-psh^𝓥 (λ {s} {γ} {P} {Q} → LnL.psh^⊢ {LnL} {s} {γ} {P} {Q})

    foo : ∀ {A z x} → z ≤ ω# * x →
      (x LnL.· LnL.[ LnL , ∞ ]_⊢ o-var x A) LnL.[ z ∙ o-var z A ]ᶜ
    foo {A} {z} {x} le with liview x | liview z
    ... | view-lin lx | view-lin lz =
      ⟨ LnL.mkᶜ {Q = [ ω# ]} [ ≤-trans le (≤-reflexive (*-comm ω# _)) ]ₙ ⟩·
        LnL.`var (LnL.lvar here refl [ ω≤1 ]ₙ)
    ... | view-lin lx | view-int =
      ⟨ LnL.mkᶜ {Q = [ ω# ]} [ ω#≤ ]ₙ ⟩·
        LnL.`con (`Ge _ , refl ,
          □ᶜ⟨ mkDup ≤*-refl [ ω#≤ ]ₙ [ ω#≤ ]ₙ (λ _ → [ ω#≤ ]ₙ) ⟩
            LnL.`var (LnL.lvar (↙ here) refl ([ ω≤1 ]ₙ ++ₙ []ₙ)))
    foo ≤-refl | view-int | view-int =
      ⟨ LnL.mkᶜ {Q = [ ω# ]} [ ≤-refl ]ₙ ⟩·
        LnL.`var (LnL.lvar here refl [ ω≤1 ]ₙ)

    bar : ∀ {A z x} → (Linear z → Linear x) →
      (x LnL.· LnL.[ LnL , ∞ ]_⊢ o-var x A) LnL.[ o-ann z x ∙ o-var z A ]ᶜ
    bar {A} {z} {x} l with liview z
    ... | view-lin lz =
      ⟨ LnL.mkᶜ {Q = [ 1# ]} [ ≤-reflexive (*-identityʳ _) ]ₙ ⟩·
          LnL.`var (LnL.lvar here eq [ ≤-refl ]ₙ)
        where
        eq : (lin , A ᵒTy) ≡ o-var x A
        eq rewrite liview-prop (liview x) (view-lin (l lz)) = refl
    ... | view-int =
      ⟨ LnL.mkᶜ {Q = [ ω# ]} [ ω#≤  ]ₙ ⟩· M
      where
      M : LnL.[ LnL , ∞ ] LnL.[ ω# ∙ (int , tG (A ᵒTy)) ]ᶜ ⊢ o-var x A
      M with liview x
      ... | view-int = LnL.`var (LnL.lvar here refl [ ω≤1 ]ₙ)
      ... | view-lin lx =
        LnL.`con $ `Ge _ , refl ,
          □ᶜ⟨ mkDup ≤*-refl [ ω≤0 ]ₙ [ ≤-refl ]ₙ (λ r → [ ω#≤ ]ₙ) ⟩
            LnL.`var (LnL.lvar (↙ here) refl ([ ω≤1 ]ₙ ++ₙ []ₙ))

  o𝓒 : LR.OpenFam 0ℓ
  o𝓒 Γ A = LnL.Term (Γ ᵒCtx) (_ , A ᵒTy)

  oreify : ∀ {Θ} →
    ∀[ LR.Kripke LR._∋_ o𝓒 Θ ⇒
       (λ Γ A → LnL.Term (Γ ᵒCtx LnL.++ᶜ Θ ᵒCtx) (_ , A ᵒTy)) ]
  oreify t = LnL.ren o-distrib-++ᶜ (LR.reify t)

  module _ where
    open LR.Semantics
    open LnL.[_]_⇒ᵉ_
    open LnL using
      ( _⇒ʳ_; ren; ↙ʳ; ↘ʳ; []ʳ; []ʳ′; _++ʳ_; _++ʳ′_; 1ʳ; _>>ʳ_
      ; _⇒ˢ_; sub; []ˢ; _++ˢ_; 1ˢ; _>>ˢ_; ren-to-sub; pw-sub
      )

    o-✴-sub : {Γ : LR.Ctx} → let LR.ctx R γ = Γ in ∀ {P Q} →
      R ≤[ P +* Q ] →
      LnL.ctx (o-ann* R P) (o-var* R γ) ⇒ˢ LR.ctx P γ ᵒCtx ×
      LnL.ctx (o-ann* R Q) (o-var* R γ) ⇒ˢ LR.ctx Q γ ᵒCtx
    o-✴-sub sp+ .proj₁ =
      pw-sub (λ i → bar (λ l → linear-summands (sp+ .get i) l .proj₁))
    o-✴-sub sp+ .proj₂ =
      pw-sub (λ i → bar (λ l → linear-summands (sp+ .get i) l .proj₂))

    oSem : LR.Semantics LR LR._∋_ o𝓒

    oSem .ren^𝓥 = LR.ren^∋

    oSem .⟦var⟧ {LR.ctx R γ} (LR.lvar i refl b) with is-lin (R i) in q
    ... | false =
      LnL.`con (`Ge _ , refl , □ᶜ⟨ mkDup ≤*-refl R≤0 R≤R+R R≤rR ⟩
          LnL.`var (LnL.lvar (↙ i) (≡.cong (if_then _ else _) q) (b ++ₙ []ₙ)))
      where
      R≤0 : R ≤0*
      R≤0 .get j with (i ≟ j) .does | (i ≟ j) .proof | b .get j
      ... | false | ofⁿ z | le = le
      ... | true | ofʸ refl | le with ω# ← R j = ω≤0

      R≤R+R : R ≤[ R +* R ]
      R≤R+R .get j = ≤0-dup (R≤0 .get j)
      R≤rR : ∀ r → R ≤[ r *ₗ R ]
      R≤rR r .get j = ≤0-scl (R≤0 .get j)
    ... | true = LnL.`var (LnL.lvar i (≡.cong (if_then _ else _) q) b)

    oSem .⟦con⟧ (`Ii , refl , ℑᶜ⟨ sp0 ⟩) = LnL.`con (`Ii , refl , ℑᶜ⟨ sp0 ⟩)
    oSem .⟦con⟧ (`Ie Z , refl , s ✴ᶜ⟨ sp+ ⟩ t) =
      let σs , σt = o-✴-sub sp+ in
      LnL.`con $ `Ie _ , refl ,
        sub (σs ++ˢ ren-to-sub o-distrib-[]ᶜ) (oreify s)
          ✴ᶜ⟨ mend-+* sp+ ⟩
        sub (σt ++ˢ ren-to-sub o-distrib-[]ᶜ) (oreify t)
    oSem .⟦con⟧ (`⊗i A B , refl , s ✴ᶜ⟨ sp+ ⟩ t) =
      let σs , σt = o-✴-sub sp+ in
      LnL.`con $ `⊗i _ _ , refl ,
        sub (σs ++ˢ ren-to-sub o-distrib-[]ᶜ) (oreify s)
          ✴ᶜ⟨ mend-+* sp+ ⟩
        sub (σt ++ˢ ren-to-sub o-distrib-[]ᶜ) (oreify t)
    oSem .⟦con⟧ (`⊗e A B Z , refl , s ✴ᶜ⟨ sp+ ⟩ t) =
      let σs , σt = o-✴-sub sp+ in
      LnL.`con $ `⊗e _ _ _ , refl ,
        sub (σs ++ˢ ren-to-sub o-distrib-[]ᶜ) (oreify s)
          ✴ᶜ⟨ mend-+* sp+ ⟩
        sub (σt ++ˢ ren-to-sub o-distrib-++ᶜ) (oreify t)
    oSem .⟦con⟧ (`⊸i A B , refl , s) = LnL.`con $ `⊸i _ _ , refl , oreify s
    oSem .⟦con⟧ (`⊸e A B , refl , s ✴ᶜ⟨ sp+ ⟩ t) =
      let σs , σt = o-✴-sub sp+ in
      LnL.`con $ `⊸e _ _ , refl ,
        sub (σs ++ˢ ren-to-sub o-distrib-[]ᶜ) (oreify s)
          ✴ᶜ⟨ mend-+* sp+ ⟩
        sub (σt ++ˢ ren-to-sub o-distrib-[]ᶜ) (oreify t)
    oSem .⟦con⟧ {ctx R γ} (`!i A , refl , ⟨ mkᶜ {P} sp* ⟩· s) =
      LnL.`con $ `Fi _ , refl ,
        □ᶜ⟨ mkDup ≤*-refl R-del R-dup R-scl ⟩
          (LnL.`con $ `Gi _ , refl ,
            □ᶜ⟨ mkDup ≤*-refl (R-del ++ₙ []ₙ) (R-dup ++ₙ []ₙ)
                (λ r → R-scl r ++ₙ []ₙ) ⟩
              sub (ren-to-sub ((1ʳ ++ʳ []ʳ′) >>ʳ ↙ʳ {δ = []}) >>ˢ
                  (pw-sub (λ i → foo (sp* .get i)) ++ˢ ren-to-sub []ʳ′))
                (oreify s))
      where
      open LnL.With-psh^𝓥 (λ {s} {γ} → LnL.psh^∋ {s} {γ})

      R-del : R ≤0*
      R-del .get i = ≤-trans (sp* .get i) (ω*-del (P i))
      R-dup : R ≤[ R +* R ]
      R-dup .get i = ≤0-dup (R-del .get i)
      R-scl : ∀ r → R ≤[ r *ₗ R ]
      R-scl r .get i = ≤0-scl (R-del .get i)
    oSem .⟦con⟧ (`!e A Z , refl , s ✴ᶜ⟨ sp+ ⟩ t) =
      let σs , σt = o-✴-sub sp+ in
      LnL.`con $ `Fe _ _ , refl ,
        sub (σs ++ˢ ren-to-sub o-distrib-[]ᶜ) (oreify s)
          ✴ᶜ⟨ mend-+* sp+ ⟩
        sub (σt ++ˢ 1ˢ) (oreify t)

  module _ where
    open LR.[_]_⇒ᵉ_
    open LR._∋_

    *-distrib-[]ᶜ : LR.[]ᶜ LR.⇒ʳ LnL.[]ᶜ *Ctx
    *-distrib-[]ᶜ .Ψ = 1ᴿ
    *-distrib-[]ᶜ .fit-here = []ₙ
    *-distrib-[]ᶜ .lookup _ (LR.lvar () q b)

    *-distrib-++ᶜ : ∀ {Γ Δ} →
      Γ *Ctx LR.++ᶜ Δ *Ctx LR.⇒ʳ (Γ LnL.++ᶜ Δ) *Ctx
    *-distrib-++ᶜ .Ψ = 1ᴿ
    *-distrib-++ᶜ .fit-here = ≤*-refl ++ₙ ≤*-refl
    *-distrib-++ᶜ .lookup _ v .idx = v .idx
    *-distrib-++ᶜ .lookup _ v .tyq with v .idx | v .tyq
    ... | ↙ i | q = q
    ... | ↘ i | q = q
    *-distrib-++ᶜ .lookup le v .basis = ≤*-trans le (v .basis)

  module _ where
    open LnL.Semantics
    open LnL.[_]_⇒ᵉ_
    open LR.[_]_⇒ᵉ_

    open LnL using (ℑᶜ⟨_⟩; _✴ᶜ⟨_⟩_; ⟨_⟩·ᶜ_; □ᶜ⟨_⟩_; mkᶜ)
    open LR using
      (_⇒ʳ_; ren; 1ʳ; _>>ʳ_; _++ʳ_; subuse-ren; ↙ʳ; ++-[]ʳ→; ++-[]ʳ←)

    *𝓒 : LnL.OpenFam 0ℓ
    *𝓒 Γ A = LR.Term (Γ *Ctx) (A *ΣTy)

    *reify : ∀ {Θ} →
      ∀[ LnL.Kripke LnL._∋_ *𝓒 Θ ⇒
         (λ Γ A → LR.Term (Γ *Ctx LR.++ᶜ Θ *Ctx) (A *ΣTy)) ]
    *reify t = LR.ren *-distrib-++ᶜ (LnL.reify t)

    *Sem : LnL.Semantics LnL LnL._∋_ *𝓒
    *Sem .ren^𝓥 = LnL.ren^∋
    *Sem .⟦var⟧ (LnL.lvar i q b) = LR.`var (LR.lvar i (≡.cong _*ΣTy q) b)
    *Sem .⟦con⟧ (`Ii , refl , ℑᶜ⟨ sp0 ⟩) = LR.`con (`Ii , refl , ℑᶜ⟨ sp0 ⟩)
    *Sem .⟦con⟧ (`Ie C , refl , s ✴ᶜ⟨ sp+ ⟩ t) =
      let ths = 1ʳ ++ʳ *-distrib-[]ᶜ in
      let tht = 1ʳ ++ʳ *-distrib-[]ᶜ in
      LR.`con (`Ie _ , refl ,
        ren ths (*reify s) ✴ᶜ⟨ sp+ ⟩ ren tht (*reify t))
    *Sem .⟦con⟧ (`⊗i A B , refl , s ✴ᶜ⟨ sp+ ⟩ t) =
      let ths = 1ʳ ++ʳ *-distrib-[]ᶜ in
      let tht = 1ʳ ++ʳ *-distrib-[]ᶜ in
      LR.`con (`⊗i _ _ , refl ,
        ren ths (*reify s) ✴ᶜ⟨ sp+ ⟩ ren tht (*reify t))
    *Sem .⟦con⟧ (`⊗e A B C , refl , s ✴ᶜ⟨ sp+ ⟩ t) =
      let ths = 1ʳ ++ʳ *-distrib-[]ᶜ in
      let tht = 1ʳ ++ʳ *-distrib-++ᶜ in
      LR.`con (`⊗e _ _ _ , refl ,
        ren ths (*reify s) ✴ᶜ⟨ sp+ ⟩ ren tht (*reify t))
    *Sem .⟦con⟧ (`⊸i A B , refl , t) =
      LR.`con (`⊸i _ _ , refl , *reify t)
    *Sem .⟦con⟧ (`⊸e A B , refl , s ✴ᶜ⟨ sp+ ⟩ t) =
      let ths = 1ʳ ++ʳ *-distrib-[]ᶜ in
      let tht = 1ʳ ++ʳ *-distrib-[]ᶜ in
      LR.`con (`⊸e _ _ , refl ,
        ren ths (*reify s) ✴ᶜ⟨ sp+ ⟩ ren tht (*reify t))
    *Sem .⟦con⟧ (`Fi X , refl , □ᶜ⟨ mkDup str sp0 sp+ sp* ⟩ t) =
      let th = subuse-ren str ++ʳ *-distrib-[]ᶜ in
      LR.`con (`!i _ , refl ,
        ⟨ (mk λ i → lemma (≤-trans (str .get i) (sp0 .get i))) ⟩·ᶜ
          ren th (*reify t))
      where
      lemma : ∀ {x} → x ≤ 0# → x ≤ ω# * x
      lemma ≤-refl = ≤-refl
      lemma ω≤0 = ≤-refl
    *Sem .⟦con⟧ (`Fe X C , refl , s ✴ᶜ⟨ sp+ ⟩ t) =
      let ths = 1ʳ ++ʳ *-distrib-[]ᶜ in
      LR.`con (`!e _ _ , refl , ren ths (*reify s) ✴ᶜ⟨ sp+ ⟩ *reify t)
    *Sem .⟦con⟧ (`1i , refl , □ᶜ⟨ mkDup str sp0 sp+ sp* ⟩ _) =
      LR.`con (`Ii , refl , ℑᶜ⟨ 0ₘ-mono str sp0 ⟩)
    *Sem .⟦con⟧ (`×i X Y , refl , □ᶜ⟨ mkDup str sp0 sp+ sp* ⟩ (s , t)) =
      let ths = ++-[]ʳ→ ++ʳ *-distrib-[]ᶜ in
      let tht = ++-[]ʳ→ ++ʳ *-distrib-[]ᶜ in
      LR.`con (`⊗i _ _ , refl ,
        LR.`con (`!i _ , refl , ⟨ sp* ω# ++ₙ []ₙ ⟩·ᶜ ren ths (*reify s))
          ✴ᶜ⟨ +ₘ-mono str ≤*-refl ≤*-refl sp+ ⟩
        LR.`con (`!i _ , refl , ⟨ sp* ω# ++ₙ []ₙ ⟩·ᶜ ren tht (*reify t)))
    *Sem .⟦con⟧ (`×e ll X Y , refl , □ᶜ⟨ mkDup str sp0 sp+ sp* ⟩ t) =
      let th = 1ʳ ++ʳ *-distrib-[]ᶜ in
      LR.`con (`⊗e _ _ _ , refl ,
        ren th (*reify t)
          ✴ᶜ⟨ +ₘ-mono str ≤*-refl ≤*-refl (+*-identity↘ _) ⟩
        LR.`con (`!e _ _ , refl ,
          LR.`var (LR.lvar (↙ (↘ (↙ here))) refl (≤*-refl ++ₙ []ₙ))
            ✴ᶜ⟨ +*-triv ++ₙ ([ ≤-refl ]ₙ ++ₙ [ ≤-refl ]ₙ) ⟩
          LR.`con (`!e _ _ , refl ,
            LR.`var (LR.lvar (↙ (↙ (↘ (↘ here)))) refl (≤*-refl ++ₙ []ₙ))
              ✴ᶜ⟨ +*-triv ++ₙ [ ω≤1 ]ₙ ⟩
            LR.`var (LR.lvar (↙ (↘ here)) refl (≤*-refl ++ₙ [ ω≤0 ]ₙ)))))
    *Sem .⟦con⟧ (`×e rr X Y , refl , □ᶜ⟨ mkDup str sp0 sp+ sp* ⟩ t) =
      let th = 1ʳ ++ʳ *-distrib-[]ᶜ in
      LR.`con (`⊗e _ _ _ , refl ,
        ren th (*reify t)
          ✴ᶜ⟨ +ₘ-mono str ≤*-refl ≤*-refl (+*-identity↘ _) ⟩
        LR.`con (`!e _ _ , refl ,
          LR.`var (LR.lvar (↙ (↘ (↙ here))) refl (≤*-refl ++ₙ []ₙ))
            ✴ᶜ⟨ +*-triv ++ₙ ([ ≤-refl ]ₙ ++ₙ [ ≤-refl ]ₙ) ⟩
          LR.`con (`!e _ _ , refl ,
            LR.`var (LR.lvar (↙ (↙ (↘ (↘ here)))) refl (≤*-refl ++ₙ []ₙ))
              ✴ᶜ⟨ +*-triv ++ₙ [ ω≤0 ]ₙ ⟩
            LR.`var (LR.lvar (↘ here) refl (≤*-refl ++ₙ [ ω≤1 ]ₙ)))))
    *Sem .⟦con⟧ (`→i X Y , refl , □ᶜ⟨ mkDup str sp0 sp+ sp* ⟩ t) =
      let th = ↙ʳ ++ʳ 1ʳ in
      LR.`con (`⊸i _ _ , refl ,
        LR.`con (`!e _ _ , refl ,
          LR.`var (LR.lvar (↙ (↘ here)) refl (≤*-refl ++ₙ []ₙ))
            ✴ᶜ⟨ ≤*→+* str ++ₙ [ ≤-refl ]ₙ ⟩
          ren th (*reify t)))
    *Sem .⟦con⟧ (`→e X Y , refl , □ᶜ⟨ mkDup str sp0 sp+ sp* ⟩ (s , t)) =
      let ths = 1ʳ ++ʳ *-distrib-[]ᶜ in
      let tht = ++-[]ʳ→ ++ʳ *-distrib-[]ᶜ in
      LR.`con (`⊸e _ _ , refl ,
        ren ths (*reify s)
          ✴ᶜ⟨ +ₘ-mono str ≤*-refl ≤*-refl sp+ ⟩
        LR.`con (`!i _ , refl , ⟨ sp* ω# ++ₙ []ₙ ⟩·ᶜ
          ren tht (*reify t)))
    *Sem .⟦con⟧ (`Gi A , refl , □ᶜ⟨ mkDup str sp0 sp+ sp* ⟩ t) =
      let th = ++-[]ʳ← >>ʳ (subuse-ren str ++ʳ *-distrib-[]ᶜ) in
      ren th (*reify t)
    *Sem .⟦con⟧ (`Ge A , refl , □ᶜ⟨ mkDup str sp0 sp+ sp* ⟩ t) =
      let th = ++-[]ʳ← >>ʳ (subuse-ren str ++ʳ *-distrib-[]ᶜ) in
      ren th (*reify t)
