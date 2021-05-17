{-# OPTIONS --safe --without-K --postfix-projections #-}

module Algebra.Po.Relation where

  open import Algebra.Po
  open import Data.Product
  open import Data.Unit
  open import Level
  open import Relation.Binary using (REL; _⇒_)
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

  module _ {c ℓ₁ ℓ₂ cm cn ℓm₁ ℓm₂ ℓn₁ ℓn₂} {R : PoSemiring c ℓ₁ ℓ₂}
           (M : PoLeftSemimodule R cm ℓm₁ ℓm₂)
           (N : PoLeftSemimodule R cn ℓn₁ ℓn₂)
    where

    open PoSemiring R
    private
      module M = PoLeftSemimodule M
      module N = PoLeftSemimodule N

    -- TODO: all of these could be less indexed and subsume things from
    -- Generic.Linear.Syntax.Interpretation.

    record 0ThenRel {r} (rel : REL M.Carrierₘ N.Carrierₘ r)
      (_ : ⊤) (z : N.Carrierₘ)
      : Set (r ⊔ cm ⊔ ℓm₁ ⊔ ℓm₂) where
      constructor _,_
      field
        {0′} : _
        sp0 : 0′ M.≤ₘ M.0ₘ
        is-rel : rel 0′ z

    record +ThenRel {r} (rel : REL M.Carrierₘ N.Carrierₘ r)
      (xy : M.Carrierₘ × M.Carrierₘ) (z : N.Carrierₘ)
      : Set (r ⊔ cm ⊔ ℓm₁ ⊔ ℓm₂) where
      constructor _,_
      private
        x = proj₁ xy; y = proj₂ xy
      field
        {x+y} : _
        sp+ : x+y M.≤ₘ x M.+ₘ y
        is-rel : rel x+y z

    record RelThen+ {r} (rel : REL M.Carrierₘ N.Carrierₘ r)
      (xy : M.Carrierₘ × M.Carrierₘ) (z : N.Carrierₘ)
      : Set (r ⊔ cn ⊔ ℓn₁ ⊔ ℓn₂) where
      constructor ⟨_,_⟩_
      private
        x = proj₁ xy; y = proj₂ xy
      field
        {x′ y′} : _
        l-rel : rel x x′
        r-rel : rel y y′
        sp+ : z N.≤ₘ x′ N.+ₘ y′

    record *ThenRel {r} (rel : REL M.Carrierₘ N.Carrierₘ r)
      (sx : Carrier × M.Carrierₘ) (z : N.Carrierₘ)
      : Set (r ⊔ cm ⊔ ℓm₁ ⊔ ℓm₂) where
      constructor _,_
      private
        s = proj₁ sx; x = proj₂ sx
      field
        {s*x} : _
        sp* : s*x M.≤ₘ s M.*ₘ x
        is-rel : rel s*x z

    record RelThen* {r} (rel : REL M.Carrierₘ N.Carrierₘ r)
      (sx : Carrier × M.Carrierₘ) (z : N.Carrierₘ)
      : Set (r ⊔ cn ⊔ ℓn₁ ⊔ ℓn₂) where
      constructor _,_
      private
        s = proj₁ sx; x = proj₂ sx
      field
        {y} : _
        is-rel : rel x y
        sp+ : z N.≤ₘ s N.*ₘ y

    record PoLeftSemimoduleRel (r : Level)
      : Set (c ⊔ cm ⊔ cn ⊔ ℓm₁ ⊔ ℓm₂ ⊔ ℓn₁ ⊔ ℓn₂ ⊔ suc r)
      where
      field
        rel : REL M.Carrierₘ N.Carrierₘ r
        rel-0ₘ : 0ThenRel rel ⇒ λ _ z → z N.≤ₘ N.0ₘ
        rel-+ₘ : +ThenRel rel ⇒ RelThen+ rel
        rel-*ₘ : *ThenRel rel ⇒ RelThen* rel

  module _ {c ℓ₁ ℓ₂ cm ℓm₁ ℓm₂} {R : PoSemiring c ℓ₁ ℓ₂}
           {M : PoLeftSemimodule R cm ℓm₁ ℓm₂}
    where

    open PoSemiring R
    private
      module M = PoLeftSemimodule M

    id-PoLeftSemimoduleRel : PoLeftSemimoduleRel M M cm
    id-PoLeftSemimoduleRel = record
      { rel = _≡_
      ; rel-0ₘ = λ where (sp0 , ≡.refl) → sp0
      ; rel-+ₘ = λ where (sp+ , ≡.refl) → ⟨ ≡.refl , ≡.refl ⟩ sp+
      ; rel-*ₘ = λ where (sp* , ≡.refl) → ≡.refl , sp*
      }
