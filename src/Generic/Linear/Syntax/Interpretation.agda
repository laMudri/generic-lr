{-# OPTIONS --safe --without-K #-}

open import Algebra
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel)

import Generic.Linear.Syntax as Syntax

module Generic.Linear.Syntax.Interpretation
  (Ty Ann : Set) (open Syntax Ty Ann) (_⊴_ : Rel Ann lzero)
  (0# : Ann) (_+_ : Op₂ Ann) (1# : Ann) (_*_ : Op₂ Ann)
  (⟦_⊢_⟧ : Ctx → Scoped)
  where

  open import Data.Product
  open import Function
  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary

  open import Data.LTree
  open import Data.LTree.Vector

  open import Generic.Linear.Operations _⊴_ 0# _+_ 1# _*_

  record _✴_ (T U : Ctx → Set) (RΓ : Ctx) : Set where
    constructor _✴⟨_⟩_
    open Ctx RΓ
    field
      {P Q} : Vector Ann _
      T-prf : T record RΓ { R = P }
      split : P +* Q ⊴* R
      U-prf : U record RΓ { R = Q }

  record _·_ (ρ : Ann) (T : Ctx → Set) (RΓ : Ctx) : Set where
    constructor ⟨_⟩·_
    open Ctx RΓ
    field
      {P} : Vector Ann _
      split : ρ *ₗ P ⊴* R
      T-prf : T record RΓ { R = P }

  record Dup (T : Ctx → Set) (RΓ : Ctx) : Set where
    constructor □⟨_,_⟩_
    open Ctx RΓ
    field
      split-0 : 0* ⊴* R
      split-+ : R +* R ⊴* R
      T-prf : T RΓ

  ⟦_⟧p : Premises → Ctx → Set
  ⟦ Γ `⊢ A ⟧p = ⟦ Γ ⊢ A ⟧
  ⟦ `⊤ ⟧p = U
  ⟦ `I ⟧p (ctx R Γ) = 0* ⊴* R
  ⟦ p `∧ q ⟧p = ⟦ p ⟧p ∩ ⟦ q ⟧p
  ⟦ p `* q ⟧p = ⟦ p ⟧p ✴ ⟦ q ⟧p
  ⟦ ρ `· p ⟧p = ρ · ⟦ p ⟧p
  ⟦ `□ p ⟧p = Dup (⟦ p ⟧p)

  ⟦_⟧r : Rule → Scoped
  ⟦ rule ps A′ ⟧r A = const (A′ ≡ A) ∩ ⟦ ps ⟧p

  ⟦_⟧s : System → Scoped
  ⟦ system L rs ⟧s A PΓ = Σ[ l ∈ L ] ⟦ rs l ⟧r A PΓ
