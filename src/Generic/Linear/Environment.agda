{-# OPTIONS --safe --without-K #-}

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
    Q ≤* P → 𝓥 (ctx P γ) ⊆ 𝓥 (ctx Q γ)

  -- Working with relations is nicer than working with functions, but to
  -- implement `map` for `□, we need the relation to be backed by a function.

  record [_]_⇒ᵉ_ (𝓥 : OpenFam ℓ) (Γ Δ : Ctx) : Set (suc 0ℓ ⊔ ℓ) where
    constructor pack

    open Ctx Γ renaming (shape to s; ty-ctx to γ; use-ctx to P)
    open Ctx Δ renaming (shape to t; ty-ctx to δ; use-ctx to Q)

    field
      Ψ : LinFuncRel s t 0ℓ
      fit-here : Ψ .rel P Q
      lookup : ∀ {P′ Q′} → Ψ .rel P′ Q′ → ctx Q′ δ ∋_ ⊆ 𝓥 (ctx P′ γ)
  open [_]_⇒ᵉ_ public

  relocate : ∀ {𝓥 : OpenFam ℓ} {s t P P′ Q Q′ γ δ} →
    (ρ : [ 𝓥 ] ctx {s} P γ ⇒ᵉ ctx {t} Q δ) → ρ .Ψ .rel P′ Q′ →
    [ 𝓥 ] ctx P′ γ ⇒ᵉ ctx Q′ δ
  relocate ρ r = record { [_]_⇒ᵉ_ ρ; fit-here = r }

  {- TODO: resurrect as an easy way to produce envs.
  record _─Env (Γ : Ctx) (𝓥 : OpenFam ℓ) (Δ : Ctx) : Set ℓ where
    constructor pack

    open Ctx Γ renaming (shape to s; ty-ctx to γ; use-ctx to P)
    open Ctx Δ renaming (shape to t; ty-ctx to δ; use-ctx to Q)

    field
      Ψ : LinMor s t
      fit-here : Q ≤* Ψ .hom P
      lookup : ∀ {A P′ Q′} → Q′ ≤* Ψ .hom P′ →
        LVar A (ctx P′ γ) → 𝓥 A (ctx Q′ δ)
  open _─Env public
  -}
