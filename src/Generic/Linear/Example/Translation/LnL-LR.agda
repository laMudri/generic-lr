{-# OPTIONS --sized-types --without-K --prop --postfix-projections #-}

module Generic.Linear.Example.Translation.LnL-LR where

  open import Algebra.Relational
  open import Algebra.Po
  open import Data.Bool.Extra
  open import Data.Hand
  open import Data.LTree
  open import Data.LTree.Vector hiding (++ˢ)
  open import Data.LTree.Matrix
  open import Data.LTree.Automation
  open import Data.Product
  open import Data.Sum
  open import Data.Unit hiding (_≤_)
  open import Data.Wrap renaming ([_] to mk)
  open import Function
  open import Function.Equality
  open import Function.Equivalence
  open import Level
  open import Proposition
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)
  open import Relation.Nary
  open import Relation.Unary.Bunched
  open import Size

  open import Generic.Linear.Example.LLFlags
  open import Generic.Linear.Example.ZeroOneMany renaming (u01ω to Ann)
  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring

  -- private open module Dummy {s} = FRelLeftSemimodule (Vᶠᴿ s)

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
  open LR using
    ( `LR; LR; ι; tI; _t⊗_; _t⊸_; t!
    ; `Ii; `Ie; `⊗i; `⊗e; `⊸i; `⊸e; `!i; `!e
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
  open LnL using
    ( `LnL; LnL; lin; int; ι; tI; _t⊗_; _t⊸_; tF; t1; _t×_; _t→_; tG
    ; `Ii; `Ie; `⊗i; `⊗e; `⊸i; `⊸e; `Fi; `Fe
    ; `1i; `×i; `×e; `→i; `→e; `Gi; `Ge
    )

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

  module _ where
    open LnL.Ctx
    open LR.Ctx

    infixl 28 _ᵒCtx _*Ctx

    _ᵒCtx : LR.Ctx → LnL.Ctx
    (Rγ ᵒCtx) .shape = Rγ .shape
    (Rγ ᵒCtx) .use-ctx = Rγ .use-ctx
    (Rγ ᵒCtx) .ty-ctx i = _ , Rγ .ty-ctx i ᵒTy

    _*Ctx : LnL.Ctx → LR.Ctx
    (Rγ *Ctx) .shape = Rγ .shape
    (Rγ *Ctx) .use-ctx = Rγ .use-ctx
    (Rγ *Ctx) .ty-ctx i = Rγ .ty-ctx i *ΣTy

  module _ where
    open LnL.[_]_⇒ᵉ_
    open LnL._∋_

    o-distrib-[]ᶜ : LnL.[]ᶜ LnL.⇒ʳ (LR.[]ᶜ ᵒCtx)
    o-distrib-[]ᶜ .Ψ = 1ᴿ
    o-distrib-[]ᶜ .fit-here = []ₙ
    o-distrib-[]ᶜ .lookup _ (LnL.lvar (there () i) q b)

    o-distrib-++ᶜ : ∀ {Γ Δ} →
      Γ ᵒCtx LnL.++ᶜ Δ ᵒCtx LnL.⇒ʳ (Γ LR.++ᶜ Δ) ᵒCtx
    o-distrib-++ᶜ .Ψ = 1ᴿ
    o-distrib-++ᶜ .fit-here = ≤*-refl ++ₙ ≤*-refl
    o-distrib-++ᶜ .lookup _ v .idx = v .idx
    o-distrib-++ᶜ .lookup _ v .tyq with v .idx | v .tyq
    ... | ↙ i | q = q
    ... | ↘ i | q = q
    o-distrib-++ᶜ .lookup le v .basis = ≤*-trans le (v .basis)

    -- uω*-Dup : ∀ {s T} {P R : Vector Ann s} → P ≤[ uω *ₗ R ] → T P → Dup ? T P
    -- uω*-Dup = ?

    o𝓒 : LR.OpenFam 0ℓ
    o𝓒 Γ A = LnL.Term (Γ ᵒCtx) (_ , A ᵒTy)

    oreify : ∀ {Θ} →
      ∀[ LR.Kripke LR._∋_ o𝓒 Θ ⇒
         (λ Γ A → LnL.Term (Γ ᵒCtx LnL.++ᶜ Θ ᵒCtx) (_ , A ᵒTy)) ]
    oreify t = LnL.ren o-distrib-++ᶜ (LR.reify t)

  module _ where
    open LR.Semantics
    open LnL.[_]_⇒ᵉ_

    open WithLLFlags using (ℑᶜ⟨_⟩; _✴ᶜ⟨_⟩_; ⟨_⟩·ᶜ_; □ᶜ⟨_⟩_; mkᶜ)

    oSem : LR.Semantics LR LR._∋_ o𝓒
    oSem .ren^𝓥 = LR.ren^∋
    oSem .⟦var⟧ (LR.lvar i refl b) = LnL.`var (LnL.lvar i refl b)
    oSem .⟦con⟧ (`Ii , refl , ℑᶜ⟨ sp0 ⟩) = LnL.`con (`Ii , refl , ℑᶜ⟨ sp0 ⟩)
    oSem .⟦con⟧ (`Ie Z , refl , s ✴ᶜ⟨ sp+ ⟩ t) =
      let ρs = LnL.1ʳ LnL.++ʳ o-distrib-[]ᶜ in
      let ρt = LnL.1ʳ LnL.++ʳ o-distrib-[]ᶜ in
      LnL.`con (`Ie _ , refl ,
        LnL.ren ρs (oreify s) ✴ᶜ⟨ sp+ ⟩ LnL.ren ρt (oreify t))
    oSem .⟦con⟧ (`⊗i A B , refl , s ✴ᶜ⟨ sp+ ⟩ t) =
      let ρs = LnL.1ʳ LnL.++ʳ o-distrib-[]ᶜ in
      let ρt = LnL.1ʳ LnL.++ʳ o-distrib-[]ᶜ in
      LnL.`con (`⊗i _ _ , refl ,
        LnL.ren ρs (oreify s) ✴ᶜ⟨ sp+ ⟩ LnL.ren ρt (oreify t))
    oSem .⟦con⟧ (`⊗e A B Z , refl , s ✴ᶜ⟨ sp+ ⟩ t) =
      let ρs = LnL.1ʳ LnL.++ʳ o-distrib-[]ᶜ in
      let ρt = LnL.1ʳ LnL.++ʳ o-distrib-++ᶜ in
      LnL.`con (`⊗e _ _ _ , refl ,
        LnL.ren ρs (oreify s) ✴ᶜ⟨ sp+ ⟩ LnL.ren ρt (oreify t))
    oSem .⟦con⟧ (`⊸i A B , refl , t) = LnL.`con (`⊸i _ _ , refl , oreify t)
    oSem .⟦con⟧ (`⊸e A B , refl , s ✴ᶜ⟨ sp+ ⟩ t) =
      let ρs = LnL.1ʳ LnL.++ʳ o-distrib-[]ᶜ in
      let ρt = LnL.1ʳ LnL.++ʳ o-distrib-[]ᶜ in
      LnL.`con (`⊸e _ _ , refl ,
        LnL.ren ρs (oreify s) ✴ᶜ⟨ sp+ ⟩ LnL.ren ρt (oreify t))
    oSem .⟦con⟧ (`!i A , refl , ⟨ mkᶜ {R} sp* ⟩· t) =
      let ρt = (ρ LnL.++ʳ o-distrib-[]ᶜ) LnL.>>ʳ LnL.++-[]ʳ→ in
      LnL.`con (`Fi _ , refl ,
        □ᶜ⟨ mkDup (*ₗ→≤* sp*) pr0 pr+ pr* ⟩
          LnL.`con (`Gi _ , refl ,
            □ᶜ⟨ mkDup ≤*-refl (pr0 ++ₙ []ₙ) (pr+ ++ₙ []ₙ)
                (λ r → pr* r ++ₙ []ₙ) ⟩
              LnL.ren ρt (oreify t)))
      where
      ρ : ∀ {s R γ} → LnL.ctx (uω *ₗ R) γ LnL.⇒ʳ LnL.ctx {s} R γ
      ρ .Ψ = 1ᴿ
      ρ {R = R} .fit-here .get i = ω*-≤ (R i)
      ρ .lookup le (LnL.lvar i q b) = LnL.lvar i q (≤*-trans le b)

      pr0 : uω *ₗ R ≤0*
      pr0 .get i = ω*-del (R i)
      pr+ : let ωR = uω *ₗ R in ωR ≤[ ωR +* ωR ]
      pr+ .get i = ω*-dup (R i)
      pr* : let ωR = uω *ₗ R in ∀ r → ωR ≤[ r *ₗ ωR ]
      pr* r .get i = ω*-scl (R i) r
    oSem .⟦con⟧ (`!e A Z , refl , s ✴ᶜ⟨ sp+ ⟩ t) =
      let ρs = LnL.1ʳ LnL.++ʳ o-distrib-[]ᶜ in
      LnL.`con (`Fe _ _ , refl ,
        LnL.ren ρs (oreify s)
          ✴ᶜ⟨ sp+ ⟩
        LnL.sub (LnL.1ˢ LnL.++ˢ σ) (oreify t))
      where
      σ : ∀ {A} →
        LnL.[ LnL ] LnL.[ uω ∙ _ , tG A ]ᶜ ⇒ˢ LnL.[ uω ∙ _ , A ]ᶜ
      σ .Ψ = [─ [ uω ] ─]ᴿ
      σ .fit-here = *ₗ-triv
      σ .lookup {P′} {Q′} le (LnL.lvar here refl b) =
        LnL.`con (`Ge _ , refl ,
          □ᶜ⟨ mkDup ≤*-refl [ P′≤0 ]ₙ [ P′≤+ ]ₙ (λ r → [ P′≤* r ]ₙ) ⟩
            LnL.`var (LnL.lvar (↙ here) refl ([ P′≤1 ]ₙ ++ₙ []ₙ)))
        where
        P′≤ω : P′ here ≤ uω
        P′≤ω = ≤-trans (le .get here) (*-mono (b .get here) ≤-refl)

        P′≤0 : P′ here ≤ u0
        P′≤0 = ≤-trans P′≤ω ω≤0
        P′≤+ : P′ here ≤ P′ here + P′ here
        P′≤+ with _ ← P′ here | ≤-refl ← P′≤ω = ≤-refl
        P′≤* : ∀ r → P′ here ≤ r * P′ here
        P′≤* r with _ ← P′ here | ≤-refl ← P′≤ω = uω≤
        P′≤1 : P′ here ≤ u1
        P′≤1 = ≤-trans P′≤ω ω≤1

  _ᵒTm : ∀ {A γ} → LR.Term γ A → LnL.Term (γ ᵒCtx) (_ , A ᵒTy)
  _ᵒTm = LR.Semantics.semantics oSem LR.identity

  module _ where
    open LR.[_]_⇒ᵉ_
    open LR._∋_

    *-distrib-[]ᶜ : LR.[]ᶜ LR.⇒ʳ LnL.[]ᶜ *Ctx
    *-distrib-[]ᶜ .Ψ = 1ᴿ
    *-distrib-[]ᶜ .fit-here = []ₙ
    *-distrib-[]ᶜ .lookup _ (LR.lvar (there () i) q b)

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
      let ths = LR.1ʳ LR.++ʳ *-distrib-[]ᶜ in
      let tht = LR.1ʳ LR.++ʳ *-distrib-[]ᶜ in
      LR.`con (`Ie _ , refl ,
        LR.ren ths (*reify s) ✴ᶜ⟨ sp+ ⟩ LR.ren tht (*reify t))
    *Sem .⟦con⟧ (`⊗i A B , refl , s ✴ᶜ⟨ sp+ ⟩ t) =
      let ths = LR.1ʳ LR.++ʳ *-distrib-[]ᶜ in
      let tht = LR.1ʳ LR.++ʳ *-distrib-[]ᶜ in
      LR.`con (`⊗i _ _ , refl ,
        LR.ren ths (*reify s) ✴ᶜ⟨ sp+ ⟩ LR.ren tht (*reify t))
    *Sem .⟦con⟧ (`⊗e A B C , refl , s ✴ᶜ⟨ sp+ ⟩ t) =
      let ths = LR.1ʳ LR.++ʳ *-distrib-[]ᶜ in
      let tht = LR.1ʳ LR.++ʳ *-distrib-++ᶜ in
      LR.`con (`⊗e _ _ _ , refl ,
        LR.ren ths (*reify s) ✴ᶜ⟨ sp+ ⟩ LR.ren tht (*reify t))
    *Sem .⟦con⟧ (`⊸i A B , refl , t) =
      LR.`con (`⊸i _ _ , refl , *reify t)
    *Sem .⟦con⟧ (`⊸e A B , refl , s ✴ᶜ⟨ sp+ ⟩ t) =
      let ths = LR.1ʳ LR.++ʳ *-distrib-[]ᶜ in
      let tht = LR.1ʳ LR.++ʳ *-distrib-[]ᶜ in
      LR.`con (`⊸e _ _ , refl ,
        LR.ren ths (*reify s) ✴ᶜ⟨ sp+ ⟩ LR.ren tht (*reify t))
    *Sem .⟦con⟧ (`Fi X , refl , □ᶜ⟨ mkDup str sp0 sp+ sp* ⟩ t) =
      let th = LR.subuse-ren str LR.++ʳ *-distrib-[]ᶜ in
      LR.`con (`!i _ , refl ,
        ⟨ (mk λ i → lemma (≤-trans (str .get i) (sp0 .get i))) ⟩·ᶜ
          LR.ren th (*reify t))
      where
      lemma : ∀ {x} → x ≤ u0 → x ≤ uω * x
      lemma ≤-refl = ≤-refl
      lemma ω≤0 = ≤-refl
    *Sem .⟦con⟧ (`Fe X C , refl , s ✴ᶜ⟨ sp+ ⟩ t) =
      let ths = LR.1ʳ LR.++ʳ *-distrib-[]ᶜ in
      LR.`con (`!e _ _ , refl , LR.ren ths (*reify s) ✴ᶜ⟨ sp+ ⟩ *reify t)
    *Sem .⟦con⟧ (`1i , refl , □ᶜ⟨ mkDup str sp0 sp+ sp* ⟩ _) =
      LR.`con (`Ii , refl , ℑᶜ⟨ 0ₘ-mono str sp0 ⟩)
    *Sem .⟦con⟧ (`×i X Y , refl , □ᶜ⟨ mkDup str sp0 sp+ sp* ⟩ (s , t)) =
      let ths = LR.++-[]ʳ→ LR.++ʳ *-distrib-[]ᶜ in
      let tht = LR.++-[]ʳ→ LR.++ʳ *-distrib-[]ᶜ in
      LR.`con (`⊗i _ _ , refl ,
        LR.`con (`!i _ , refl , ⟨ sp* uω ++ₙ []ₙ ⟩·ᶜ LR.ren ths (*reify s))
          ✴ᶜ⟨ +ₘ-mono str ≤*-refl ≤*-refl sp+ ⟩
        LR.`con (`!i _ , refl , ⟨ sp* uω ++ₙ []ₙ ⟩·ᶜ LR.ren tht (*reify t)))
    *Sem .⟦con⟧ (`×e ll X Y , refl , □ᶜ⟨ mkDup str sp0 sp+ sp* ⟩ t) =
      let th = LR.1ʳ LR.++ʳ *-distrib-[]ᶜ in
      LR.`con (`⊗e _ _ _ , refl ,
        LR.ren th (*reify t)
          ✴ᶜ⟨ +ₘ-mono str ≤*-refl ≤*-refl (+*-identity↘ _) ⟩
        LR.`con (`!e _ _ , refl ,
          LR.`var (LR.lvar (↙ (↘ (↙ here))) refl (≤*-refl ++ₙ []ₙ))
            ✴ᶜ⟨ +*-triv ++ₙ ([ ≤-refl ]ₙ ++ₙ [ ≤-refl ]ₙ) ⟩
          LR.`con (`!e _ _ , refl ,
            LR.`var (LR.lvar (↙ (↙ (↘ (↘ here)))) refl (≤*-refl ++ₙ []ₙ))
              ✴ᶜ⟨ +*-triv ++ₙ [ ω≤1 ]ₙ ⟩
            LR.`var (LR.lvar (↙ (↘ here)) refl (≤*-refl ++ₙ [ ω≤0 ]ₙ)))))
    *Sem .⟦con⟧ (`×e rr X Y , refl , □ᶜ⟨ mkDup str sp0 sp+ sp* ⟩ t) =
      let th = LR.1ʳ LR.++ʳ *-distrib-[]ᶜ in
      LR.`con (`⊗e _ _ _ , refl ,
        LR.ren th (*reify t)
          ✴ᶜ⟨ +ₘ-mono str ≤*-refl ≤*-refl (+*-identity↘ _) ⟩
        LR.`con (`!e _ _ , refl ,
          LR.`var (LR.lvar (↙ (↘ (↙ here))) refl (≤*-refl ++ₙ []ₙ))
            ✴ᶜ⟨ +*-triv ++ₙ ([ ≤-refl ]ₙ ++ₙ [ ≤-refl ]ₙ) ⟩
          LR.`con (`!e _ _ , refl ,
            LR.`var (LR.lvar (↙ (↙ (↘ (↘ here)))) refl (≤*-refl ++ₙ []ₙ))
              ✴ᶜ⟨ +*-triv ++ₙ [ ω≤0 ]ₙ ⟩
            LR.`var (LR.lvar (↘ here) refl (≤*-refl ++ₙ [ ω≤1 ]ₙ)))))
    *Sem .⟦con⟧ (`→i X Y , refl , □ᶜ⟨ mkDup str sp0 sp+ sp* ⟩ t) =
      let th = LR.↙ʳ LR.++ʳ LR.1ʳ in
      LR.`con (`⊸i _ _ , refl ,
        LR.`con (`!e _ _ , refl ,
          LR.`var (LR.lvar (↙ (↘ here)) refl (≤*-refl ++ₙ []ₙ))
            ✴ᶜ⟨ ≤*→+* str ++ₙ [ ≤-refl ]ₙ ⟩
          LR.ren th (*reify t)))
    *Sem .⟦con⟧ (`→e X Y , refl , □ᶜ⟨ mkDup str sp0 sp+ sp* ⟩ (s , t)) =
      let ths = LR.1ʳ LR.++ʳ *-distrib-[]ᶜ in
      let tht = LR.++-[]ʳ→ LR.++ʳ *-distrib-[]ᶜ in
      LR.`con (`⊸e _ _ , refl ,
        LR.ren ths (*reify s)
          ✴ᶜ⟨ +ₘ-mono str ≤*-refl ≤*-refl sp+ ⟩
        LR.`con (`!i _ , refl , ⟨ sp* uω ++ₙ []ₙ ⟩·ᶜ
          LR.ren tht (*reify t)))
    *Sem .⟦con⟧ (`Gi A , refl , □ᶜ⟨ mkDup str sp0 sp+ sp* ⟩ t) =
      let th = (LR.subuse-ren str LR.++ʳ *-distrib-[]ᶜ) LR.>>ʳ LR.++-[]ʳ← in
      LR.ren th (*reify t)
    *Sem .⟦con⟧ (`Ge A , refl , □ᶜ⟨ mkDup str sp0 sp+ sp* ⟩ t) =
      let th = (LR.subuse-ren str LR.++ʳ *-distrib-[]ᶜ) LR.>>ʳ LR.++-[]ʳ← in
      LR.ren th (*reify t)
