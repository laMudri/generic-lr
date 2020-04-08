{-# OPTIONS --safe --without-K #-}

-- Functional matrices, like the vectors in Data.LTree.Vector

module Data.LTree.Matrix where

  open import Data.Bool using (if_then_else_)
  open import Data.LTree
  open import Data.LTree.Vector
  open import Function.Base using (id; _∘_; _∘′_)
  open import Level using (Level; _⊔_)
  open import Relation.Binary using (REL)
  open import Relation.Unary using (Pred)

  private
    variable
      a b c r : Level
      A : Set a
      B : Set b
      C : Set c
      R : REL A B r
      s s′ t t′ u : LTree

  Matrix : Set a → (s t : LTree) → Set a
  Matrix A s t = Vector (Vector A t) s

  _ᵀ : Matrix A s t → Matrix A t s
  (M ᵀ) i j = M j i

  module Ident (0# 1# : A) where
    1ᴹ : Matrix A s s
    1ᴹ i j = if i == j then 1# else 0#
  open Ident public renaming (1ᴹ to ident)

  module Mult (0# : C) (_+_ : C → C → C) (_*_ : A → B → C) where
    open Sum 0# _+_

    infixr 7 _*ᴹ_
    _*ᴹ_ : Matrix A s t → Matrix B t u → Matrix C s u
    _*ᴹ_ M N i k = ∑ λ j → M i j * N j k

  open Mult public renaming (_*ᴹ_ to mult)

  -- Pointwise

  lift₀ᴹ : A → ∀ {s t} → Matrix A s t
  lift₀ᴹ f = lift₀ (lift₀ f)

  lift₁ᴹ : (A → B) → ∀ {s t} → Matrix A s t → Matrix B s t
  lift₁ᴹ f = lift₁ (lift₁ f)

  lift₂ᴹ : (A → B → C) → ∀ {s t} → Matrix A s t → Matrix B s t → Matrix C s t
  lift₂ᴹ f = lift₂ (lift₂ f)

  record Lift₁ᴹ (R : Pred A r) {s} (u : Matrix A s t) : Set r where
    constructor mk
    field get : ∀ i j → R (u i j)
  open Lift₁ᴹ public

  record Lift₂ᴹ (R : REL A B r) {s t} (u : Matrix A s t) (v : Matrix B s t)
               : Set r where
    constructor mk
    field get : ∀ i j → R (u i j) (v i j)
  open Lift₂ᴹ public

  module Zero (0# : A) where
    0ᴹ = lift₀ᴹ 0#

  module Plus (_+_ : A → B → C) where
    infixr 6 _+ᴹ_
    _+ᴹ_ = lift₂ᴹ _+_

  module LeftScale (_*_ : A → B → C) where
    infixr 7 _*ₗ_
    _*ₗ_ : A → Matrix B s t → Matrix C s t
    x *ₗ M = lift₁ᴹ (x *_) M

  -- Accessing rows/cols

  getrow : Matrix A s t → Ptr s → Vector A t
  getrow M i = M i
  getcol : Matrix A s t → Ptr t → Vector A s
  getcol M j i = M i j

  getrowL₂ : {M : Matrix A s t} {N : Matrix B s t} →
             Lift₂ᴹ R M N → (i : Ptr s) → Lift₂ R (getrow M i) (getrow N i)
  getrowL₂ MN i .get j = MN .get i j
  getcolL₂ : {M : Matrix A s t} {N : Matrix B s t} →
             Lift₂ᴹ R M N → (j : Ptr t) → Lift₂ R (getcol M j) (getcol N j)
  getcolL₂ MN j .get i = MN .get i j

  -- Block matrix operations

  row : Vector A t → Matrix A [-] t
  row v = [ v ]
  col : Vector A s → Matrix A s [-]
  col u = lift₁ [_] u

  rowL₂ : {u : Vector A t} {v : Vector B t} →
          Lift₂ R u v → Lift₂ᴹ R (row u) (row v)
  rowL₂ uv .get _ i = uv .get i

  unrow : Matrix A [-] t → Vector A t
  unrow M = un[-] M
  uncol : Matrix A s [-] → Vector A s
  uncol M = lift₁ un[-] M

  unrowL₂ : {u : Vector A t} {v : Vector B t} →
            Lift₂ᴹ R (row u) (row v) → Lift₂ R u v
  unrowL₂ uv .get i = uv .get here i

  [─] : Matrix A ε t
  [─] = []

  [_─_] : Matrix A s t → Matrix A s′ t → Matrix A (s <+> s′) t
  [ M ─ N ] = M ++ N

  [│] : Matrix A s ε
  [│] = lift₀ []

  [_│_] : Matrix A s t → Matrix A s t′ → Matrix A s (t <+> t′)
  [ M │ N ] = lift₂ _++_ M N

  topᴹ : Matrix A (s <+> s′) t → Matrix A s t
  topᴹ M i j = M (↙ i) j
  botᴹ : Matrix A (s <+> s′) t → Matrix A s′ t
  botᴹ M i j = M (↘ i) j

  leftᴹ : Matrix A s (t <+> t′) → Matrix A s t
  leftᴹ M i j = M i (↙ j)
  rightᴹ : Matrix A s (t <+> t′) → Matrix A s t′
  rightᴹ M i j = M i (↘ j)

  -- Block matrix operations for equations
  -- TODO: deprecate in favour of rowL₂, unrowL₂, &c.

  row-cong₂ : ∀ {u : Vector A t} {v : Vector B t} →
              Lift₂ R u v → Lift₂ᴹ R (row u) (row v)
  row-cong₂ (mk uv) = mk (λ _ j → uv j)
  col-cong₂ : ∀ {u : Vector A s} {v : Vector B s} →
              Lift₂ R u v → Lift₂ᴹ R (col u) (col v)
  col-cong₂ (mk uv) = mk (λ i _ → uv i)

  unrow-cong₂ : ∀ {M : Matrix A [-] t} {N : Matrix B [-] t} →
                Lift₂ᴹ R M N → Lift₂ R (unrow M) (unrow N)
  unrow-cong₂ (mk MN) = mk (λ j → MN here j)
  uncol-cong₂ : ∀ {M : Matrix A s [-]} {N : Matrix B s [-]} →
                Lift₂ᴹ R M N → Lift₂ R (uncol M) (uncol N)
  uncol-cong₂ (mk MN) = mk (λ i → MN i here)

  private
    vertical-block : Matrix A s t → Matrix A s′ t → Matrix A (s <+> s′) t
    vertical-block M N =
      [ M
        ─
        N ]
