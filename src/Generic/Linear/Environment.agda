{-# OPTIONS --safe --without-K --prop #-}

open import Algebra.Po
open import Level
open import Relation.Binary using (Rel)

module Generic.Linear.Environment
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring renaming (Carrier to Ann; _≤_ to _⊴_)

  open import Data.LTree
  open import Data.LTree.Vector

  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring

  open import Data.Product
  open import Function using (_∘_; _⇔_; Equivalence)
  open import Relation.Unary

  infix 20 [_]_⇒ᵉ_

  private
    variable
      Γ Δ : Ctx
      T : Ctx → Set
      ℓ : Level
      𝓥 : Scoped ℓ

  -- TODO: this probably should be somewhere else.
  IsPresheaf : Scoped ℓ → Set ℓ
  IsPresheaf 𝓥 =
    ∀ {s} {γ : Vector Ty s} {P Q} →
    Q ⊴* P → ∀[ 𝓥 (ctx P γ) ⇒ 𝓥 (ctx Q γ) ]

  -- Working with relations is nicer than working with functions, but to
  -- implement `map` for `□, we need the relation to be backed by a function.

  record [_]_⇒ᵉ_ (𝓥 : Scoped ℓ) (Γ Δ : Ctx) : Set (suc 0ℓ ⊔ ℓ) where
    constructor pack

    open Ctx Γ renaming (shape to s; ty-ctx to γ; use-ctx to P)
    open Ctx Δ renaming (shape to t; ty-ctx to δ; use-ctx to Q)

    field
      M : LinMor t s
      asLinRel : AsLinRel M 0ℓ
    private
      Mᴿ = asLinRel .linRel
    field
      sums : Mᴿ .rel Q P
      lookup : ∀ {P′ Q′} → Mᴿ .rel Q′ P′ → ∀[ ctx Q′ δ ∋_ ⇒ 𝓥 (ctx P′ γ) ]

    sums-⊴* : P ⊴* M .hom Q
    sums-⊴* = asLinRel .equiv .f sums
      where open Equivalence
  open [_]_⇒ᵉ_ public

  {- TODO: resurrect as an easy way to produce envs.
  record _─Env (Γ : Ctx) (𝓥 : Scoped ℓ) (Δ : Ctx) : Set ℓ where
    constructor pack

    open Ctx Γ renaming (shape to s; ty-ctx to γ; use-ctx to P)
    open Ctx Δ renaming (shape to t; ty-ctx to δ; use-ctx to Q)

    field
      M : LinMor s t
      sums : Q ⊴* M .hom P
      lookup : ∀ {A P′ Q′} → Q′ ⊴* M .hom P′ →
        LVar A (ctx P′ γ) → 𝓥 A (ctx Q′ δ)
  open _─Env public
  -}
