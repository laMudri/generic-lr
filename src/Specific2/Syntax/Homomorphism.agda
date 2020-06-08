{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ)

module Specific2.Syntax.Homomorphism
  {Dom Cod : SkewSemiring 0ℓ 0ℓ} (f : SkewSemiringMor Dom Cod) where

  open SkewSemiringMor f
  import Specific2.Syntax.Prelude as Pre
  open import Specific2.Syntax as Syn
    using (tι; tI; t⊤; t0; _t⊸_; _t⊗_; _t⊕_; _t&_; t!
          ; ivar; ivar!; lvar; lvar!
          ; var; app; lam; unm; uni; prm; ten
          ; exf; cse; inl; inr; top; prl; prr; wth; bam; bng)
  open import Generic.Linear.Syntax as Gen using (ctx)

  import Specific2.Syntax.Renaming as Ren
  import Specific2.Syntax.Subuse as Subuse

  open import Data.Bool.Base
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.Product
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; cong)
  open import Relation.Nullary using (Dec; does; proof)

  private
    module Dom where
      open Pre Dom public
      open Syn Ann _⊴_ 0# _+_ 1# _*_ public
      open Gen Ty Ann public hiding (ctx→sctx)
      open Ren Dom public
      open Subuse Dom public

    module Cod where
      open Pre Cod public
      open Syn Ann _⊴_ 0# _+_ 1# _*_ public
      open Gen Ty Ann public hiding (ctx→sctx)
      open Ren Cod public
      open Subuse Cod public

  hom-1ᴹ : ∀ {s} → lift₁ᴹ apply Dom.1ᴹ Cod.⊴ᴹ Cod.1ᴹ {s = s}
  hom-1ᴹ .get i j with does (i ≟ j)
  ... | false = hom-0#
  ... | true = hom-1#

  hom-ty : Dom.Ty → Cod.Ty
  hom-ty tι = tι
  hom-ty tI = tI
  hom-ty t⊤ = t⊤
  hom-ty t0 = t0
  hom-ty (A t⊸ B) = hom-ty A t⊸ hom-ty B
  hom-ty (A t⊗ B) = hom-ty A t⊗ hom-ty B
  hom-ty (A t⊕ B) = hom-ty A t⊕ hom-ty B
  hom-ty (A t& B) = hom-ty A t& hom-ty B
  hom-ty (t! ρ A) = t! (apply ρ) (hom-ty A)

  hom-ctx : Dom.Ctx → Cod.Ctx
  hom-ctx (ctx R Γ) = ctx (lift₁ apply R) (lift₁ hom-ty Γ)

  hom-var : ∀ {RΓ A} → Dom.LVar RΓ A → Cod.LVar (hom-ctx RΓ) (hom-ty A)
  hom-var (lvar i q sp) = lvar i (cong hom-ty q)
    (mk λ j → Cod.⊴-trans (hom-mono (sp .get j)) (hom-1ᴹ .get i j))

  -- hom-bind : ∀ {PΓ t Q Δ A} →
  --            Cod.Tm (hom-ctx PΓ Cod.++ᶜ ctx {s = t} Q (lift₁ hom-ty Δ)) A →
  --            Cod.Tm (hom-ctx PΓ Cod.++ᶜ hom-ctx (ctx Q Δ)) A
  -- hom-bind = ?

  module _ where
    open Pre Cod
    open Cod.Ren

    hom-bind : ∀ {s t P Q} {Γ : Vector Dom.Ty s} {Δ : Vector Dom.Ty t} → Cod.Ren
               (ctx (lift₁ apply P ++ lift₁ apply Q) (lift₁ hom-ty Γ ++ lift₁ hom-ty Δ))
               (ctx (lift₁ apply (P ++ Q)) (lift₁ hom-ty (Γ ++ Δ)))
    hom-bind .act (ivar i@(↙ _) q) = ivar i q
    hom-bind .act (ivar i@(↘ _) q) = ivar i q
    hom-bind {P = P} {Q} .use-pres .get (↙ i) =
      ⊴-trans (+.identity-→ .proj₂ _)
              (+.mono (*ᴹ-1ᴹ (row (lift₁ apply P)) .get here i)
                      (*ᴹ-0ᴹ (row (lift₁ apply Q)) .get here i))
    hom-bind {P = P} {Q} .use-pres .get (↘ i) =
      ⊴-trans (+.identity-← .proj₁ _)
              (+.mono (*ᴹ-0ᴹ (row (lift₁ apply P)) .get here i)
                      (*ᴹ-1ᴹ (row (lift₁ apply Q)) .get here i))

  hom-tm : ∀ {RΓ A} → Dom.Tm RΓ A → Cod.Tm (hom-ctx RΓ) (hom-ty A)
  hom-tm (var x) = var (hom-var x)
  hom-tm (app M N sp) = {!!}
  hom-tm {ctx R Γ} (lam M) =
    -- Problem: need 1# ⊴ apply 1#, which goes against the grain of the other
    -- homomorphism laws.              ↓↓↓
    lam (Cod.subuse (Cod.⊴*-refl ++₂ [ {!!} ]₂) (Cod.ren hom-bind (hom-tm M)))
  hom-tm (unm M N sp) = {!!}
  hom-tm (uni sp) = uni (mk λ i → Cod.⊴-trans (hom-mono (sp .get i)) hom-0#)
  hom-tm (prm M N sp) = prm (hom-tm M) {!hom-tm N!}
    (mk λ i → Cod.⊴-trans (hom-mono (sp .get i)) (hom-+ _ _))
  hom-tm (ten M N sp) = ten (hom-tm M) (hom-tm N)
    (mk λ i → Cod.⊴-trans (hom-mono (sp .get i)) (hom-+ _ _))
  hom-tm (exf M sp) = {!!}
  hom-tm (cse M N O sp) = {!!}
  hom-tm (inl M) = inl (hom-tm M)
  hom-tm (inr M) = inr (hom-tm M)
  hom-tm top = top
  hom-tm (prl M) = prl (hom-tm M)
  hom-tm (prr M) = prr (hom-tm M)
  hom-tm (wth M N) = wth (hom-tm M) (hom-tm N)
  hom-tm (bam M N sp) = bam (hom-tm M) (Cod.ren hom-bind (hom-tm N))
    (mk λ i → Cod.⊴-trans (hom-mono (sp .get i)) (hom-+ _ _))
  hom-tm (bng M sp) = bng (hom-tm M)
    (mk λ i → Cod.⊴-trans (hom-mono (sp .get i)) (hom-* _ _))
