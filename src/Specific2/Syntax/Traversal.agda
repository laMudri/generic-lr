{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ)

module Specific2.Syntax.Traversal (algebra : SkewSemiring 0ℓ 0ℓ) where

  open import Specific2.Syntax.Prelude algebra

  open import Specific2.Syntax Ann _⊴_ 0# _+_ 1# _*_
  open import Generic.Linear.Syntax Ty Ann

  open import Data.LTree
  open import Data.LTree.Vector using (Vector; _++_; Lift₂; mk; get; _++₂_)
  open import Data.LTree.Matrix
    using (Matrix; unrow; row; unrowL₂; rowL₂; getrowL₂; [_─_]; [_│_])
  open import Data.Product
  open import Relation.Binary.PropositionalEquality

  private
    variable
      s t u : LTree
      A B C : Ty
      PΓ QΔ RΘ : Ctx
      T : Ctx → Ty → Set
      M : Matrix Ann t s

  record Env (T : Ctx → Ty → Set) (M : Matrix Ann t s)
         (Γ : Vector Ty s) (Δ : Vector Ty t) : Set where
    field act : (j : IVar Δ A) → T (ctx (M (j .idx)) Γ) A
  open Env public

  record Compat (M : Matrix Ann t s) P Q : Set where
    constructor mk
    field get : P ⊴* unrow (row Q *ᴹ M)
  open Compat public

  obv : ∀ {Q} → Compat M (unrow (row Q *ᴹ M)) Q
  obv = mk ⊴*-refl

  record DeployedEnv (T : Ctx → Ty → Set) (PΓ : Ctx) (QΔ : Ctx) : Set where
    open Ctx PΓ renaming (s to γ; Γ to Γ; R to P)
    open Ctx QΔ renaming (s to δ; Γ to Δ; R to Q)
    field
      matrix : Matrix Ann δ γ
      env : Env T matrix Γ Δ
      compat : Compat matrix P Q
  open DeployedEnv public

  private
    variable
      r : Ann
      P P′ Pl Pr : Vector Ann s
      Q Q′ Ql Qr : Vector Ann t
      R : Vector Ann u
      Γ : Vector Ty s
      Δ Θ : Vector Ty t

  record Kit (T : Ctx → Ty → Set) : Set where
    field
      psh : P ⊴* P′ → T (ctx P′ Γ) A → T (ctx P Γ) A
      vr : LVar PΓ A → T PΓ A
      tm : T PΓ A → Tm PΓ A
      wk : T PΓ A → T (PΓ ++ᶜ ctx 0* Θ) A

  fixup-0 : Compat M P Q → Q ⊴* 0* → P ⊴* 0*
  fixup-0 {M = M} (mk com) sp =
    (⊴*-trans com (unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp) ⊴ᴹ-refl)
                           (0ᴹ-*ᴹ M))))

  fixup-+ : Compat M P Q → Q ⊴* Ql +* Qr →
            P ⊴* unrow (row Ql *ᴹ M) +* unrow (row Qr *ᴹ M)
  fixup-+ {M = M} (mk com) sp =
    (⊴*-trans com (unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp) ⊴ᴹ-refl)
                           (+ᴹ-*ᴹ _ _ M))))

  fixup-* : Compat M P Q → Q ⊴* r *ₗ Q′ →
            P ⊴* r *ₗ unrow (row Q′ *ᴹ M)
  fixup-* {M = M} (mk com) sp =
    (⊴*-trans com (unrowL₂ (⊴ᴹ-trans (*ᴹ-mono (rowL₂ sp) ⊴ᴹ-refl)
                           (*ₗ-*ᴹ _ _ M))))

  bindMat : Matrix Ann t s → Matrix Ann (t <+> u) (s <+> u)
  bindMat M = [ [ M  │ 0ᴹ ]
                     ─
                [ 0ᴹ │ 1ᴹ ] ]

  bindCompat : Compat M P Q → Compat (bindMat M) (P ++ R) (Q ++ R)
  bindCompat {Q = Q} {R = R} com .get =
    ⊴*-trans (mk λ i → +.identity-→ .proj₂ _)
             (+*-mono (com .get) (unrowL₂ (*ᴹ-0ᴹ (row R))))
    ++₂
    ⊴*-trans (mk λ i → +.identity-← .proj₁ _)
             (+*-mono (unrowL₂ (*ᴹ-0ᴹ (row Q))) (unrowL₂ (*ᴹ-1ᴹ (row R))))

  module _ (K : Kit T) where
    open Kit K

    bindEnv : Env T M Γ Δ → Env T (bindMat M) (Γ ++ Θ) (Δ ++ Θ)
    bindEnv ρ .act (ivar! (↙ j)) = wk (ρ .act (ivar! j))
    bindEnv ρ .act (ivar! (↘ j)) = vr (lvar! (↘ j) (⊴*-refl ++₂ ⊴*-refl))

    trav : Env T M Γ Δ → Compat M P Q → Tm (ctx Q Δ) A → Tm (ctx P Γ) A
    trav ρ (mk com) (var (lvar! j sp)) = tm
      (psh (⊴*-trans com
                     (⊴*-trans (unrowL₂ (*ᴹ-mono (rowL₂ sp) ⊴ᴹ-refl))
                               (getrowL₂ (1ᴹ-*ᴹ _) j)))
           (ρ .act (ivar! j)))
    trav ρ com (app s t sp) =
      app (trav ρ obv s) (trav ρ obv t) (fixup-+ com sp)
    trav ρ com (lam t) = lam (trav (bindEnv ρ) (bindCompat com) t)
    trav ρ com (unm s t sp) =
      unm (trav ρ obv s) (trav ρ obv t) (fixup-+ com sp)
    trav ρ com (uni sp) = uni (fixup-0 com sp)
    trav ρ com (prm s t sp) =
      prm (trav ρ obv s) (trav (bindEnv ρ) (bindCompat obv) t) (fixup-+ com sp)
    trav ρ com (ten s t sp) =
      ten (trav ρ obv s) (trav ρ obv t) (fixup-+ com sp)
    trav ρ com (exf t sp) = exf (trav ρ obv t) (fixup-+ com sp)
    trav ρ com (cse s t u sp) =
      cse (trav ρ obv s) (trav (bindEnv ρ) (bindCompat obv) t)
          (trav (bindEnv ρ) (bindCompat obv) u) (fixup-+ com sp)
    trav ρ com (inl t) = inl (trav ρ com t)
    trav ρ com (inr t) = inr (trav ρ com t)
    trav ρ com top = top
    trav ρ com (prl t) = prl (trav ρ com t)
    trav ρ com (prr t) = prr (trav ρ com t)
    trav ρ com (wth s t) = wth (trav ρ com s) (trav ρ com t)
    trav ρ com (bam s t sp) =
      bam (trav ρ obv s) (trav (bindEnv ρ) (bindCompat obv) t) (fixup-+ com sp)
    trav ρ com (bng t sp) = bng (trav ρ obv t) (fixup-* com sp)

    travD : DeployedEnv T PΓ QΔ → Tm QΔ A → Tm PΓ A
    travD ρ t = trav (ρ .env) (ρ .compat) t
