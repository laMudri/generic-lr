{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra using (Op₂)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)

module Specific.Syntax
  (Ann : Set) (_⊴_ : Rel Ann 0ℓ)
  (0# : Ann) (_+_ : Op₂ Ann) (1# : Ann) (_*_ : Op₂ Ann)
  where

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Relation.Binary.PropositionalEquality

  open Ident 0# 1#

  private
    variable
      π ρ : Ann
      t : LTree

  infix 4 _⊴*_ _⊴ᴹ_
  infixr 6 _+*_
  infixr 7 _*ₗ_

  _⊴*_ = Lift₂ _⊴_
  _⊴ᴹ_ = Lift₂ᴹ _⊴_
  0* = lift₀ 0#
  _+*_ = lift₂ _+_
  _*ₗ_ : Ann → Vector Ann t → Vector Ann t
  ρ *ₗ R = lift₁ (ρ *_) R

  infixr 5 _t⊸_
  infixr 6 _t&_ _t⊕_
  infixr 7 _t⊗_

  data Ty : Set where
    tι : Ty
    tI t⊤ t0 : Ty
    _t⊸_ _t⊗_ _t⊕_ _t&_ : (A B : Ty) → Ty
    t! : (ρ : Ann) (A : Ty) → Ty

  private
    variable
      A B C : Ty

  open import Generic.Linear.Syntax Ty Ann
  open Ctx public renaming (s to shape; R to use-ctx; Γ to ty-ctx)

  record LVar (PΓ : Ctx) (A : Ty) : Set where
    constructor lvar
    private
      s = PΓ .shape ; P = PΓ .use-ctx ; Γ = PΓ .ty-ctx
    field
      idx : Ptr s
      basis : P ⊴* 1ᴹ idx
      ty-eq : Γ idx ≡ A
  open LVar public

  private
    variable
      P Q R : Vector Ann _

  data Tm (RΓ : Ctx) : Ty → Set where
    var : LVar RΓ A → Tm RΓ A

    app : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) (A t⊸ B)) (N : Tm (ctx Q Γ) A)
          (sp : R ⊴* P +* Q) → Tm RΓ B
    lam : (M : Tm (RΓ ++ᶜ [ 1# · A ]ᶜ) B) → Tm RΓ (A t⊸ B)

    unm : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) tI) (N : Tm (ctx Q Γ) C) (sp : R ⊴* P +* Q) →
          Tm RΓ C
    uni : let ctx R Γ = RΓ in (sp : R ⊴* 0*) → Tm RΓ tI
    prm : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) (A t⊗ B))
          (N : Tm (ctx Q Γ ++ᶜ ([ 1# · A ]ᶜ ++ᶜ [ 1# · B ]ᶜ)) C)
          (sp : R ⊴* P +* Q) → Tm RΓ C
    ten : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) A) (N : Tm (ctx Q Γ) B) (sp : R ⊴* P +* Q) →
          Tm RΓ (A t⊗ B)

    exf : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) t0) (sp : R ⊴* P +* Q) → Tm RΓ C
    -- no t0 introduction
    cse : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) (A t⊕ B))
          (N : Tm (ctx Q Γ ++ᶜ [ 1# · A ]ᶜ) C)
          (O : Tm (ctx Q Γ ++ᶜ [ 1# · B ]ᶜ) C)
          (sp : R ⊴* P +* Q) → Tm RΓ C
    inl : (M : Tm RΓ A) → Tm RΓ (A t⊕ B)
    inr : (M : Tm RΓ B) → Tm RΓ (A t⊕ B)

    -- no t⊤ elimination
    top : Tm RΓ t⊤
    prl : (M : Tm RΓ (A t& B)) → Tm RΓ A
    prr : (M : Tm RΓ (A t& B)) → Tm RΓ B
    wth : (M : Tm RΓ A) (N : Tm RΓ B) → Tm RΓ (A t& B)

    bam : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) (t! ρ A)) (N : Tm (ctx Q Γ ++ᶜ ([ ρ · A ]ᶜ)) C)
          (sp : R ⊴* P +* Q) → Tm RΓ C
    bng : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) A) (sp : R ⊴* ρ *ₗ P) → Tm RΓ (t! ρ A)
