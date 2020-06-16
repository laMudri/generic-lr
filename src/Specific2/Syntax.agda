{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra using (Op₂)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)

module Specific2.Syntax
  (Ann : Set) (_⊴_ : Rel Ann 0ℓ)
  (0# : Ann) (_+_ : Op₂ Ann) (1# : Ann) (_*_ : Op₂ Ann)
  where

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.Product using (_×_; _,_)
  open import Relation.Binary.PropositionalEquality

  open Ident 0# 1#

  private
    variable
      p q r : Ann
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
    _t⊸_ : (rA : Ann × Ty) (B : Ty) → Ty
    _t⊗_ _t⊕_ : (pA qB : Ann × Ty) → Ty
    _t&_ : (A B : Ty) → Ty
    t! : (rA : Ann × Ty) → Ty

  private
    variable
      A B C : Ty
      rA pA qB : Ann × Ty

  open import Generic.Linear.Syntax Ty Ann
  open Ctx public renaming (s to shape; R to use-ctx; Γ to ty-ctx)

  record IVar {s} (Γ : Vector Ty s) (A : Ty) : Set where
    constructor ivar
    field
      idx : Ptr s
      ty-eq : Γ idx ≡ A

  record LVar (PΓ : Ctx) (A : Ty) : Set where
    constructor lvar
    private
      s = PΓ .shape ; P = PΓ .use-ctx ; Γ = PΓ .ty-ctx
    field
      idx : Ptr s
      ty-eq : Γ idx ≡ A
      basis : P ⊴* 1ᴹ idx

    iVar : IVar Γ A
    iVar .IVar.idx = idx
    iVar .IVar.ty-eq = ty-eq

  pattern ivar! i = ivar i refl
  pattern lvar! i sp = lvar i refl sp

  open IVar public
  open LVar public

  equip-var : ∀ {s Γ R} (i : IVar Γ A) → R ⊴* 1ᴹ (i .idx) →
              LVar (ctx {s} R Γ) A
  equip-var i sp .idx = i .idx
  equip-var i sp .ty-eq = i .ty-eq
  equip-var i sp .basis = sp

  private
    variable
      P Q R : Vector Ann _

  data Tm (RΓ : Ctx) : Ty → Set where
    var : LVar RΓ A → Tm RΓ A

    app : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) ((r , A) t⊸ B)) (N : Tm (ctx Q Γ) A)
          (sp : R ⊴* P +* r *ₗ Q) → Tm RΓ B
    lam : (M : Tm (RΓ ++ᶜ [ rA ]ᶜ) B) → Tm RΓ (rA t⊸ B)

    unm : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) tI) (N : Tm (ctx Q Γ) C) (sp : R ⊴* P +* Q) →
          Tm RΓ C
    uni : let ctx R Γ = RΓ in (sp : R ⊴* 0*) → Tm RΓ tI
    prm : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) (pA t⊗ qB))
          (N : Tm (ctx Q Γ ++ᶜ ([ pA ]ᶜ ++ᶜ [ qB ]ᶜ)) C)
          (sp : R ⊴* P +* Q) → Tm RΓ C
    ten : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) A) (N : Tm (ctx Q Γ) B)
          (sp : R ⊴* p *ₗ P +* q *ₗ Q) →
          Tm RΓ ((p , A) t⊗ (q , B))

    exf : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) t0) (sp : R ⊴* P +* Q) → Tm RΓ C
    -- no t0 introduction
    cse : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) (pA t⊕ qB))
          (N : Tm (ctx Q Γ ++ᶜ [ pA ]ᶜ) C)
          (O : Tm (ctx Q Γ ++ᶜ [ qB ]ᶜ) C)
          (sp : R ⊴* P +* Q) → Tm RΓ C
    inl : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) A) (sp : R ⊴* p *ₗ P) → Tm RΓ ((p , A) t⊕ qB)
    inr : let ctx R Γ = RΓ in
          (M : Tm (ctx Q Γ) B) (sp : R ⊴* q *ₗ Q) → Tm RΓ (pA t⊕ (q , B))

    -- no t⊤ elimination
    top : Tm RΓ t⊤
    prl : (M : Tm RΓ (A t& B)) → Tm RΓ A
    prr : (M : Tm RΓ (A t& B)) → Tm RΓ B
    wth : (M : Tm RΓ A) (N : Tm RΓ B) → Tm RΓ (A t& B)

    bam : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) (t! rA)) (N : Tm (ctx Q Γ ++ᶜ ([ rA ]ᶜ)) C)
          (sp : R ⊴* P +* Q) → Tm RΓ C
    bng : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) A) (sp : R ⊴* r *ₗ P) → Tm RΓ (t! (r , A))
