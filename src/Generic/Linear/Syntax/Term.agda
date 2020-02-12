{-# OPTIONS --safe --without-K #-}

open import Algebra
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary

import Generic.Linear.Syntax as Syntax

module Generic.Linear.Syntax.Term
  (Ty Ann : Set) (open Syntax Ty Ann) (_⊴_ : Rel Ann lzero)
  (0# : Ann) (_+_ : Op₂ Ann) (1# : Ann) (_*_ : Op₂ Ann)
  (⟦_⊢_⟧ : Ctx → Scoped)
  where

  open import Data.Product
  open import Function
  open import Relation.Binary.PropositionalEquality
  open import Relation.Ternary.Separation
  open import Relation.Unary

  open import Data.LTree
  open import Data.LTree.Vector

  open import Generic.Linear.Operations _⊴_ 0# _+_ 1# _*_

  rawSep : ∀ {s} → RawSep (Vector Ann s)
  rawSep = record { _⊎_≣_ = λ { P Q R → P +* Q ⊴* R } }

  open module RS {s} = RawSep (rawSep {s})

  ⟦_⟧p : Premises → Scoped
  ⟦ Γ `⊢ A ⟧p A′ = const (A ≡ A′) ∩ ⟦ Γ ⊢ A ⟧
  ⟦ `⊤ ⟧p A = U
  ⟦ `I ⟧p A (ctx R Γ) = 0* ⊴* R
  ⟦ p `∧ q ⟧p A = ⟦ p ⟧p A ∩ ⟦ q ⟧p A
  ⟦ p `* q ⟧p A = {!⟦ p ⟧p A ✴ ?!}
  ⟦ ρ `· p ⟧p A = {!!}
  ⟦ `□ p ⟧p A = {!!}
