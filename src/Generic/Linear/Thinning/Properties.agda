{-# OPTIONS --safe --without-K #-}

open import Algebra.Core
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel; IsPreorder)

module Generic.Linear.Thinning.Properties
  (Ty Ann : Set) (_≈_ : Rel Ann 0ℓ) (_⊴_ : Rel Ann 0ℓ)
  (0# : Ann) (_+_ : Op₂ Ann) (1# : Ann) (_*_ : Op₂ Ann)
  (⊴-isPreorder : IsPreorder _≈_ _⊴_)
  where

  open import Data.Product
  open import Data.Sum
  open import Function.Base using (flip)
  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.LTree.Matrix.Properties
  open Ident 0# 1#
  open Mult 0# _+_ _*_

  open import Generic.Linear.Operations _⊴_ 0# _+_ 1# _*_
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Environment Ty Ann _⊴_ 0# _+_ 1# _*_
  open import Generic.Linear.Thinning Ty Ann _⊴_ 0# _+_ 1# _*_

  open _─Env
  open Var
  open LVar

  open IsPreorder ⊴-isPreorder using () renaming
    ( refl to ⊴-refl
    ; trans to ⊴-trans
    )

  private
    variable
      PΓ QΔ RΘ : Ctx
      T : Ctx → Set
      𝓥 : Scoped
      s t u : LTree
      P Q R : Vector Ann s
      A : Ty

  -- TODO: refactor
  ⊴*-refl : P ⊴* P
  ⊴*-refl .get i = ⊴-refl
  ⊴*-trans : P ⊴* Q → Q ⊴* R → P ⊴* R
  ⊴*-trans PQ QR .get i = ⊴-trans (PQ .get i) (QR .get i)
  open Reflᴹ _⊴_ ⊴-refl renaming (reflᴹ to ⊴ᴹ-refl)

  data Thinning-cols (th : Thinning PΓ QΔ) (j : Ptr (Ctx.s QΔ)) : Set where
    is-basis : (v : Var A (Ctx.Γ PΓ)) (vq : th .lookup v .idx ≡ j)
               (les : ∀ i → th .M i j ⊴ 1ᴹ i (v .idx)) → Thinning-cols th j
    is-zero : (¬v : (v : Var A (Ctx.Γ PΓ)) → th .lookup v .idx ≢ j)
              (les : ∀ i → th .M i j ⊴ 0#) → Thinning-cols th j

  thinning-cols :
    ∀ {PΓ QΔ} (th : Thinning PΓ QΔ) (j : Ptr (Ctx.s QΔ)) → Thinning-cols th j
  thinning-cols th j = {!!}

  thinning-sub-1ᴹ :
    ∀ {PΓ QΔ A}
    (th : Thinning PΓ QΔ) (v : Var A (Ctx.Γ PΓ)) →
    M th (idx v) ⊴* 1ᴹ (idx (lookup th v))
  thinning-sub-1ᴹ {ctx {s} P Γ} {ctx {[-]} Q Δ} th v = th .lookup v .basis
  thinning-sub-1ᴹ {ctx {s} P Γ} {ctx {ε} Q Δ} th v .get (there () _)
  thinning-sub-1ᴹ {ctx {s} P Γ} {ctx {tl <+> tr} Q Δ} th v .get (go-left j)
    with th .lookup v .idx
  ... | go-left j′ = {!thinning-sub-1ᴹ ? v .get j!}
  ... | go-right j′ = {!!}
  thinning-sub-1ᴹ {ctx {s} P Γ} {ctx {tl <+> tr} Q Δ} th v .get (go-right j) =
    {!!}

  thinning-action :
    ∀ {PΓ QΔ u A}
    (th : Thinning PΓ QΔ) (N : Matrix Ann _ u) (v : Var A (Ctx.Γ PΓ)) →
    (M th *ᴹ N) (idx v) ⊴* N (idx (lookup th v))
  thinning-action {ctx {s} P Γ} {ctx {[-]} Q Δ} (pack M sums lookup) N v@(var i tyq) .get k =
    let lvar j q (mk bs) = lookup v in
    {!bs!}
  thinning-action {ctx {s} P Γ} {ctx {ε} Q Δ} (pack M sums lookup) N v@(var i tyq) .get k = {!!}
  thinning-action {ctx {s} P Γ} {ctx {tl <+> tr} Q Δ} (pack M sums lookup) N v@(var i tyq) .get k = {!!}

  identity : Thinning PΓ PΓ
  M identity = 1ᴹ
  sums (identity {PΓ}) .get j = *ᴹ-1ᴹ (row (Ctx.R PΓ)) .get here j
    where
    open MultIdent 0# 1# (flip _⊴_) 0# _+_ _*_ ⊴-refl (flip ⊴-trans)
                   {!!} {!!} {!!} {!!}
  idx (lookup identity v) = idx v
  tyq (lookup identity v) = tyq v
  basis (lookup identity v) = ⊴*-refl

  select : Thinning PΓ QΔ → (QΔ ─Env) 𝓥 RΘ → (PΓ ─Env) 𝓥 RΘ
  M (select th ρ) = M th *ᴹ M ρ
  sums (select {PΓ = PΓ} {QΔ} th ρ) =
    ⊴*-trans (sums ρ)
             (unrow-cong₂ (⊴ᴹ-trans (*ᴹ-cong (row-cong₂ (sums th)) ⊴ᴹ-refl)
                                    (*ᴹ-*ᴹ-→ (row (Ctx.R PΓ)) (M th) (M ρ))))
    where
    open Mult-cong 0# _+_ _*_ _⊴_ _⊴_ _⊴_ ⊴-refl {!!} {!!}
    open MultMult _⊴_ 0# _+_ 0# _+_ 0# _+_ _*_ _*_ _*_ _*_ ⊴-refl ⊴-trans
                  {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}
  lookup (select th ρ) v = {!lookup ρ (plain-var (lookup th v))!}

  extend : ∀ {QΔ} → Ctx.R QΔ ⊴* 0* → Thinning PΓ (PΓ ++ᶜ QΔ)
  M (extend les) i (go-left j) = 1ᴹ i j
  M (extend les) i (go-right j) = 0#
  sums (extend les) .get (go-left j) = *ᴹ-1ᴹ (row _) .get here j
    where
    open MultIdent 0# 1# (flip _⊴_) 0# _+_ _*_ ⊴-refl (flip ⊴-trans)
                   {!!} {!!} {!!} {!!}
  sums (extend {PΓ} {QΔ} les) .get (go-right j) =
    ⊴-trans (les .get j) (*ᴹ-0ᴹ (row (Ctx.R PΓ)) .get here j)
    where
    open MultZero 0# (flip _⊴_) 0# _+_ _*_ ⊴-refl (flip ⊴-trans)
                  {!!} {!!} {!!}
  idx (lookup (extend les) v) = go-left (idx v)
  tyq (lookup (extend les) v) = tyq v
  basis (lookup (extend les) v) .get (go-left j) = ⊴-refl
  basis (lookup (extend les) v) .get (go-right j) = ⊴-refl

  extract : ∀[ □ T ⇒ T ]
  extract t = t identity

  duplicate : ∀[ □ T ⇒ □ (□ T) ]
  duplicate t ρ σ = t (select ρ σ)

  th^□ : Thinnable (□ T)
  th^□ = duplicate
