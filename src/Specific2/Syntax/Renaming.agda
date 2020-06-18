{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ)

module Specific2.Syntax.Renaming
  {Dom Cod : SkewSemiring 0ℓ 0ℓ} (f : SkewSemiringMor Dom Cod) where

  private
    open module f = SkewSemiringMor f
  import Specific2.Syntax.Prelude as Pre
  open import Specific2.Syntax as Syn
    using ( ivar; ivar!; lvar; lvar!; var; shape; use-ctx; ty-ctx
          ; idx; ty-eq; basis)
  open import Generic.Linear.Syntax as Gen using (ctx)

  open import Specific2.Syntax.Traversal f

  open import Algebra.Skew.Construct.Vector
  open import Data.LTree
  open import Data.LTree.Vector using (Vector; mk; get; _++₂_; module Sum)
  open import Data.LTree.Vector.Properties
  open import Data.LTree.Matrix using (unrow; row)
  open import Data.Product
  open import Function.Base
  open import Relation.Binary.PropositionalEquality

  private
    module Dom where
      open Pre Dom public
      open Syn Ann _⊴_ 0# _+_ 1# _*_ public
      open Gen Ty Ann public hiding (ctx→sctx)

    module Cod where
      open Pre Cod public
      open Syn Ann _⊴_ 0# _+_ 1# _*_ public
      open Gen Ty Ann public hiding (ctx→sctx)
      open Sum 0# _+_ public
      open SumCong _⊴_ 0# _+_ ⊴-refl +-mono public renaming (∑-cong to ∑-mono)
      open Sum0 _⊴_ 0# _+_ ⊴-trans ⊴-refl +-mono (+.identity-→ .proj₁ 0#)
        public
      open Sum+ _⊴_ 0# _+_ ⊴-refl ⊴-trans
                +-mono (+.identity-← .proj₁ 0#) +.inter public
      open SumLinear 0# _+_ (flip _⊴_) 0# _+_ ⊴-refl (flip ⊴-trans) +-mono
        public

  -- private
  --   variable
  --     A B C : Ty
  --     PΓ QΔ RΘ : Ctx

  record Ren (PΓ : Cod.Ctx) (QΔ : Dom.Ctx) : Set where
    private
      s = PΓ .shape ; P = PΓ .use-ctx ; Γ = PΓ .ty-ctx
      t = QΔ .shape ; Q = QΔ .use-ctx ; Δ = QΔ .ty-ctx
    open Cod
    field
      act : ∀ {A} → Dom.IVar Δ A → Cod.IVar Γ (hom-ty A)
      use-pres : P ⊴* λ i → ∑ λ j → apply (Q j) * ⟨ act (ivar! j) .idx ∣ i
  open Ren public

  module _ where
    open Kit

    LVar-kit : Kit Cod.LVar
    LVar-kit .psh PQ v = Cod.equip-var (Cod.iVar v) (Cod.⊴*-trans PQ (v .basis))
    LVar-kit .vr = id
    LVar-kit .tm = var
    LVar-kit .wk v .idx = ↙ (v .idx)
    LVar-kit .wk v .ty-eq = v .ty-eq
    LVar-kit .wk v .basis = v .basis ++₂ Cod.⊴*-refl

  module _ {PΓ QΔ} (let s = PΓ .shape) (let t = QΔ .shape) where
    open SkewLeftSemimoduleMor
    open ProsetMor
    open Cod

    renMap : Ren PΓ QΔ → LinMap f t s
    renMap r .prosetMor .apply v i =
      ∑ λ j → f.apply (v j) * ⟨ r .act (ivar! j) .idx ∣ i
    renMap r .prosetMor .hom-mono vv .get i =
      ∑-mono (mk λ j → *-mono (f.hom-mono (vv .get j)) ⊴-refl)
    renMap r .hom-0ₘ .get i =
      ⊴-trans (∑-mono {t} (mk λ j → ⊴-trans (*-mono f.hom-0# ⊴-refl)
                                            (annihil .proj₁ _)))
              (∑-0 t)
    renMap r .hom-+ₘ u v .get i =
      ⊴-trans (∑-mono {t} (mk λ j → ⊴-trans (*-mono (f.hom-+ _ _) ⊴-refl)
                                            (distrib .proj₁ _ _ _)))
              (∑-+ {t} _ _)
    renMap r .hom-*ₘ p v .get i =
      ⊴-trans (∑-mono {t} (mk λ j → ⊴-trans (*-mono (f.hom-* _ _) ⊴-refl)
                                            (*.assoc _ _ _)))
              (∑-linear (f.apply p *_) (annihil .proj₂ _) (distrib .proj₂ _)
                        {t} _)

  ren : ∀ {PΓ QΔ A} → Ren PΓ QΔ → Dom.Tm QΔ A → Cod.Tm PΓ (hom-ty A)
  ren r = trav LVar-kit {M = renMap r}
    (λ { .act w@(ivar! j) → Cod.equip-var (r .act w) (mk λ i →
      ⊴-trans (∑-mono (mk λ j′ → *-mono (hom-⟨ j ∣ .get j′) ⊴-refl))
              (lemma (λ j′ → ⟨ r .act (ivar! j′) .idx ∣ i) j)) })
    (mk (r .use-pres))
    where
    open Cod

    -- TODO: put this with all the other sum lemmas
    lemma : ∀ {s} (v : Vector Ann s) i → (∑ λ j → ⟨ i ∣ j * v j) ⊴ v i
    lemma v here = *.identity .proj₁ _
    lemma {s <+> t} v (↙ i) =
      ⊴-trans (+-mono (lemma (v ∘ ↙) i)
                      (⊴-trans (∑-mono (mk λ j → annihil .proj₁ (v (↘ j))))
                               (∑-0 t)))
              (+.identity-← .proj₂ _)
    lemma {s <+> t} v (↘ i) =
      ⊴-trans (+-mono (⊴-trans (∑-mono (mk (λ j → annihil .proj₁ (v (↙ j)))))
                               (∑-0 s))
                      (lemma (v ∘ ↘) i))
              (+.identity-→ .proj₁ _)
