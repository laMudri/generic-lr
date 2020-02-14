{-# OPTIONS --safe --sized-types --without-K #-}

open import Algebra
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel)

import Generic.Linear.Syntax as Syntax

module Generic.Linear.Syntax.Term
  (Ty Ann : Set) (open Syntax Ty Ann) (_⊴_ : Rel Ann lzero)
  (0# : Ann) (_+_ : Op₂ Ann) (1# : Ann) (_*_ : Op₂ Ann)
  where

  open import Data.Product
  open import Function
  open import Size
  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary

  open import Data.LTree
  open import Data.LTree.Vector

  open import Generic.Linear.Operations _⊴_ 0# _+_ 1# _*_
  import Generic.Linear.Syntax.Interpretation as Interp′
  module Interp = Interp′ Ty Ann _⊴_ 0# _+_ 1# _*_
  open import Generic.Linear.Environment Ty Ann _⊴_ 0# _+_ 1# _*_
  open import Generic.Linear.Thinning Ty Ann _⊴_ 0# _+_ 1# _*_

  private
    variable
     A : Ty
     sz : Size

  data Tm (d : System) : Size → Scoped where
    `var : ∀[   LVar A ⇒ Tm d (↑ sz) A ]
    `con : let open Interp (Scope (Tm d sz)) in
           ∀[ ⟦ d ⟧s A ⇒ Tm d (↑ sz) A ]
