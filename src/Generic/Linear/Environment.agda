{-# OPTIONS --safe --without-K --prop #-}

open import Algebra.Po
open import Level

module Generic.Linear.Environment
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring renaming (Carrier to Ann)

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
      𝓥 : OpenFam ℓ

  -- TODO: this probably should be somewhere else.
  IsPresheaf : OpenFam ℓ → Set ℓ
  IsPresheaf 𝓥 =
    ∀ {s} {γ : Vector Ty s} {P Q} →
    Q ≤* P → ∀[ 𝓥 (ctx P γ) ⇒ 𝓥 (ctx Q γ) ]

  -- Working with relations is nicer than working with functions, but to
  -- implement `map` for `□, we need the relation to be backed by a function.

  record [_]_⇒ᵉ_ (𝓥 : OpenFam ℓ) (Γ Δ : Ctx) : Set (suc 0ℓ ⊔ ℓ) where
    constructor pack

    open Ctx Γ renaming (shape to s; ty-ctx to γ; use-ctx to P)
    open Ctx Δ renaming (shape to t; ty-ctx to δ; use-ctx to Q)

    field
      Ψ : LinMor t s
      asLinRel : AsLinRel Ψ 0ℓ
    Ψᴿ = asLinRel .linRel
    field
      sums : Ψᴿ .rel Q P
      lookup : ∀ {P′ Q′} → Ψᴿ .rel Q′ P′ → ∀[ ctx Q′ δ ∋_ ⇒ 𝓥 (ctx P′ γ) ]

    sums-≤* : P ≤* Ψ .hom Q
    sums-≤* = asLinRel .equiv .f sums
      where open Equivalence
  open [_]_⇒ᵉ_ public

  {- TODO: resurrect as an easy way to produce envs.
  record _─Env (Γ : Ctx) (𝓥 : OpenFam ℓ) (Δ : Ctx) : Set ℓ where
    constructor pack

    open Ctx Γ renaming (shape to s; ty-ctx to γ; use-ctx to P)
    open Ctx Δ renaming (shape to t; ty-ctx to δ; use-ctx to Q)

    field
      Ψ : LinMor s t
      sums : Q ≤* Ψ .hom P
      lookup : ∀ {A P′ Q′} → Q′ ≤* Ψ .hom P′ →
        LVar A (ctx P′ γ) → 𝓥 A (ctx Q′ δ)
  open _─Env public
  -}
