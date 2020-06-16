{-# OPTIONS --safe --without-K #-}

open import Algebra
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel)

import Generic.Linear.Syntax as Syntax

module Generic.Linear.Syntax.Interpretation
  (Ty Ann : Set) (open Syntax Ty Ann) (_⊴_ : Rel Ann lzero)
  (0# : Ann) (_+_ : Op₂ Ann) (1# : Ann) (_*_ : Op₂ Ann)
  where

  open import Data.Product
  open import Data.Unit
  open import Function
  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary

  open import Data.LTree
  open import Data.LTree.Vector

  open import Generic.Linear.Operations _⊴_ 0# _+_ 1# _*_

  infixr 8 _─✴_
  infixr 9 _✴_
  infixr 10 _·_

  record ✴1 (RΓ : Ctx) : Set where
    constructor ✴1⟨_⟩
    open Ctx RΓ
    field
      split : R ⊴* 0*

  record _✴_ (T U : Ctx → Set) (RΓ : Ctx) : Set where
    constructor _✴⟨_⟩_
    open Ctx RΓ
    field
      {P Q} : Vector Ann _
      T-prf : T record RΓ { R = P }
      split : R ⊴* P +* Q
      U-prf : U record RΓ { R = Q }

  record _─✴_ (T U : Ctx → Set) (RΓ : Ctx) : Set where
    constructor lam✴
    open Ctx RΓ
    field
      app✴ : ∀ {P Q} (split : Q ⊴* R +* P) (T-prf : T record RΓ { R = P }) →
             U record RΓ { R = Q }
  open _─✴_ public

  record _·_ (ρ : Ann) (T : Ctx → Set) (RΓ : Ctx) : Set where
    constructor ⟨_⟩·_
    open Ctx RΓ
    field
      {P} : Vector Ann _
      split : R ⊴* ρ *ₗ P
      T-prf : T record RΓ { R = P }

  record Dup (T : Ctx → Set) (RΓ : Ctx) : Set where
    constructor □⟨_,_⟩_
    open Ctx RΓ
    field
      split-0 : 0* ⊴* R
      split-+ : R +* R ⊴* R
      T-prf : T RΓ

  module WithScope (⟦_⊢_⟧ : Ctx → Scoped) where

    ⟦_⟧p′ : Premises → Ctx → Set
    ⟦ Γ `⊢ A ⟧p′ = ⟦ Γ ⊢ A ⟧
    ⟦ `⊤ ⟧p′ = U
    ⟦ `I ⟧p′ (ctx R Γ) = 0* ⊴* R
    ⟦ p `∧ q ⟧p′ = ⟦ p ⟧p′ ∩ ⟦ q ⟧p′
    ⟦ p `* q ⟧p′ = ⟦ p ⟧p′ ✴ ⟦ q ⟧p′
    ⟦ ρ `· p ⟧p′ = ρ · ⟦ p ⟧p′
    ⟦ `□ p ⟧p′ = Dup (⟦ p ⟧p′)

    ⟦_⟧r′ : Rule → Scoped
    ⟦ rule ps A′ ⟧r′ A = const (A′ ≡ A) ∩ ⟦ ps ⟧p′

    ⟦_⟧s′ : System → Scoped
    ⟦ system L rs ⟧s′ A PΓ = Σ[ l ∈ L ] ⟦ rs l ⟧r′ A PΓ

  ⟦_⟧p : Premises → (Ctx → Scoped) → (Ctx → Set)
  ⟦ ps ⟧p Sc = let open WithScope Sc in ⟦ ps ⟧p′

  ⟦_⟧r : Rule → (Ctx → Scoped) → Scoped
  ⟦ r ⟧r Sc = let open WithScope Sc in ⟦ r ⟧r′

  ⟦_⟧s : System → (Ctx → Scoped) → Scoped
  ⟦ s ⟧s Sc = let open WithScope Sc in ⟦ s ⟧s′

  map-p : {X Y : Ctx → Scoped} (ps : Premises) →
          (∀ {PΓ A} → ∀[ X PΓ A ⇒ Y PΓ A ]) →
          ∀[ ⟦ ps ⟧p X ⇒ ⟦ ps ⟧p Y ]
  map-p (PΓ `⊢ A) f t = f t
  map-p `⊤ f t = t
  map-p `I f t = t
  map-p (ps `∧ qs) f (s , t) = map-p ps f s , map-p qs f t
  map-p (ps `* qs) f (s ✴⟨ split ⟩ t) = map-p ps f s ✴⟨ split ⟩ map-p qs f t
  map-p (ρ `· ps) f (⟨ split ⟩· t) = ⟨ split ⟩· map-p ps f t
  map-p (`□ ps) f (□⟨ split-0 , split-+ ⟩ t) =
    □⟨ split-0 , split-+ ⟩ (map-p ps f t)

  map-r : {X Y : Ctx → Scoped} (r : Rule) →
          (∀ {PΓ A} → ∀[ X PΓ A ⇒ Y PΓ A ]) →
          ∀ {A} → ∀[ ⟦ r ⟧r X A ⇒ ⟦ r ⟧r Y A ]
  map-r (rule ps A) f (q , t) = q , map-p ps f t

  map-s : {X Y : Ctx → Scoped} (s : System) →
          (∀ {PΓ A} → ∀[ X PΓ A ⇒ Y PΓ A ]) →
          ∀ {A} → ∀[ ⟦ s ⟧s X A ⇒ ⟦ s ⟧s Y A ]
  map-s (system L rs) f (l , t) = l , (map-r (rs l) f t)
