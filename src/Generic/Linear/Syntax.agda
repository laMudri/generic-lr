
{-# OPTIONS --safe --without-K #-}

module Generic.Linear.Syntax (Ty Ann : Set) where

  open import Data.Bool.Base
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.Product using (_×_; _,_)
  open import Data.Unit.Polymorphic using (⊤; tt)
  open import Level
  open import Function.Base using (_∘_; _⟨_⟩_)
  open import Relation.Unary

  infix 25 _++ᶜ_

  record SizedCtx (s : LTree) : Set where
    constructor sctx
    field
      use-ctx : Vector Ann s
      ty-ctx : Vector Ty s

  record Ctx : Set where
    constructor ctx
    field
      {shape} : LTree
      use-ctx : Vector Ann shape
      ty-ctx : Vector Ty shape

    ctx→sctx : SizedCtx shape
    ctx→sctx = sctx use-ctx ty-ctx
  open Ctx public

  sctx→ctx : ∀ {s} → SizedCtx s → Ctx
  sctx→ctx (sctx P γ) = ctx P γ

  []ᶜ : Ctx
  []ᶜ = ctx [] []

  [_]ᶜ : Ann × Ty → Ctx
  [(r , A)]ᶜ = ctx [ r ] [ A ]

  [_·_]ᶜ : Ann → Ty → Ctx
  [ ρ · A ]ᶜ = ctx [ ρ ] [ A ]

  _++ᶜ_ : Ctx → Ctx → Ctx
  ctx P γ ++ᶜ ctx Q δ = ctx (P ++ Q) (γ ++ δ)

  IfConcat : ∀ {ℓ} → Ctx → Set ℓ → Set ℓ
  IfConcat (ctx {[-]} P γ) X = ⊤
  IfConcat (ctx {ε} P γ) X = ⊤
  IfConcat (ctx {s <+> t} P γ) X = X

  leftᶜ : (Γ : Ctx) → IfConcat Γ Ctx
  leftᶜ (ctx {[-]} P γ) = _
  leftᶜ (ctx {ε} P γ) = _
  leftᶜ (ctx {s <+> t} P γ) = ctx {s} (P ∘ ↙) (γ ∘ ↙)

  rightᶜ : (Γ : Ctx) → IfConcat Γ Ctx
  rightᶜ (ctx {[-]} P γ) = _
  rightᶜ (ctx {ε} P γ) = _
  rightᶜ (ctx {s <+> t} P γ) = ctx {t} (P ∘ ↘) (γ ∘ ↘)

  leftᶜ′ : ∀ {s t} → SizedCtx (s <+> t) → Ctx
  leftᶜ′ (sctx P γ) = ctx (P ∘ ↙) (γ ∘ ↙)

  rightᶜ′ : ∀ {s t} → SizedCtx (s <+> t) → Ctx
  rightᶜ′ (sctx P γ) = ctx (P ∘ ↘) (γ ∘ ↘)


-- Premises to each rule form a tree.
-- At each leaf is a premise, which binds one Ctx's worth of new variables.
-- Annotations are shared out to the premises via separation logic
-- connectives:
-- \begin{verbatim}
-- \item separating conjunction (`I, _`*_) – e.g, ⊗-introduction
-- \item sharing conjunction (`⊤, _`∧_)    – e.g, &-introduction
-- \item scaling (_`·_)                    – e.g, !-introduction
-- \item the duplicable modality (`□)      – e.g, recursion rules
-- \end{verbatim}


  infix 1 _=⇒_ _▹_
  infixr 2 _`✴_
  infixr 2 _`∧_
  infixr 3 _`·_




  data Premises : Set where
    ⟨_`⊢_⟩ : (Δ : Ctx) (A : Ty) → Premises
    `⊤ : Premises
    _`∧_ : (p q : Premises) → Premises
    `ℑ : Premises
    _`✴_ : (p q : Premises) → Premises
    _`·_ : (r : Ann) (p : Premises) → Premises



    `□ : (p : Premises) → Premises




  record Rule : Set where
    constructor _=⇒_
    field
      premises : Premises
      conclusion : Ty





  record System : Set₁ where
    constructor _▹_
    field
      Label : Set
      rules : (l : Label) → Rule




  open Rule public
  open System public




  OpenType : ∀ ℓ → Set (suc ℓ)
  OpenType ℓ = Ctx → Set ℓ

  _─OpenFam_ : ∀ {i} → Set i → ∀ ℓ → Set (i ⊔ suc ℓ)
  I ─OpenFam ℓ = Ctx → I → Set ℓ
  OpenFam : ∀ ℓ → Set (suc ℓ)
  OpenFam ℓ = Ty ─OpenFam ℓ

  _─ExtOpenFam_ : ∀ {i} → Set i → ∀ ℓ → Set (i ⊔ suc ℓ)
  I ─ExtOpenFam ℓ = Ctx → I ─OpenFam ℓ
  ExtOpenFam : ∀ ℓ → Set (suc ℓ)
  ExtOpenFam ℓ = Ty ─ExtOpenFam ℓ





  Scope : ∀ {i} {I : Set i} {ℓ} → I ─OpenFam ℓ → I ─ExtOpenFam ℓ
  Scope T Δ Γ A = T (Γ ++ᶜ Δ) A
