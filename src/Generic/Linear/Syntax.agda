{-# OPTIONS --safe --without-K #-}

module Generic.Linear.Syntax (Ty Ann : Set) where

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.Product using (_×_; _,_)
  open import Function.Base using (_∘_)
  open import Relation.Unary

  infix 2 _`⊢_
  infixr 3 _`*_
  infixr 4 _`∧_
  infixr 5 _`·_

  record SizedCtx (s : LTree) : Set where
    constructor sctx
    field
      R : Vector Ann s
      Γ : Vector Ty s

  record Ctx : Set where
    constructor ctx
    field
      {s} : LTree
      R : Vector Ann s
      Γ : Vector Ty s

    ctx→sctx : SizedCtx s
    ctx→sctx = sctx R Γ
  open Ctx public using (ctx→sctx)

  sctx→ctx : ∀ {s} → SizedCtx s → Ctx
  sctx→ctx (sctx P Γ) = ctx P Γ

  []ᶜ : Ctx
  []ᶜ = ctx [] []

  [_]ᶜ : Ann × Ty → Ctx
  [(r , A)]ᶜ = ctx [ r ] [ A ]

  [_·_]ᶜ : Ann → Ty → Ctx
  [ ρ · A ]ᶜ = ctx [ ρ ] [ A ]

  _++ᶜ_ : Ctx → Ctx → Ctx
  ctx P Γ ++ᶜ ctx Q Δ = ctx (P ++ Q) (Γ ++ Δ)

  leftᶜ : ∀ {s t} → SizedCtx (s <+> t) → Ctx
  leftᶜ (sctx P Γ) = ctx (P ∘ ↙) (Γ ∘ ↙)

  rightᶜ : ∀ {s t} → SizedCtx (s <+> t) → Ctx
  rightᶜ (sctx P Γ) = ctx (P ∘ ↘) (Γ ∘ ↘)

  -- Premises to each rule form a tree.
  -- At each leaf is a premise, which binds one Ctx's worth of new variables.
  -- Annotations are shared out to the premises via separation logic
  -- connectives:
  -- * separating conjunction (`I, _`*_) – e.g, ⊗-introduction
  -- * sharing conjunction (`⊤, _`∧_)    – e.g, &-introduction
  -- * scaling (_`·_)                    – e.g, !-introduction
  -- * the duplicable modality (`□)      – e.g, recursion rules

  data Premises : Set where
    _`⊢_ : (PΓ : Ctx) (A : Ty) → Premises
    `⊤ `I : Premises
    _`∧_ _`*_ : (p q : Premises) → Premises
    _`·_ : (ρ : Ann) (p : Premises) → Premises
    -- `□ : (p : Premises) → Premises

  record Rule : Set where
    constructor rule
    field
      premises : Premises
      conclusion : Ty
  open Rule public

  record System : Set₁ where
    constructor system
    field
      Label : Set
      rules : (l : Label) → Rule
  open System public

  Scoped : Set₁
  Scoped = Ty → Ctx → Set

  Scope : Scoped → Ctx → Scoped
  Scope T QΔ A = (_++ᶜ QΔ) ⊢ T A
