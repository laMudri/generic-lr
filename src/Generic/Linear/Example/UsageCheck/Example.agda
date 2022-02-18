{-# OPTIONS --sized-types --without-K --postfix-projections #-}

module Generic.Linear.Example.UsageCheck.Example where

  open import Generic.Linear.Example.ZeroOneMany
    renaming (u0 to 0#; u1 to 1#; uω to ω#)
  open import Generic.Linear.Example.PaperExamples
  open CPP0 poSemiring hiding (⊸I; !I; !E; ⊕I; ⊕E)

  open import Algebra.Po
  open import Algebra.Po.Construct.Nat
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.Product
  open import Data.Unit using (⊤; tt)
  open import Level
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
  open import Relation.Unary.Bunched
  open import Size

  open import Data.LTree.Automation
  open import Data.Nat using (ℕ)
  open import Data.Nat.Properties using (_<?_)
  open import Relation.Nullary.Decidable using (True)

  open import Generic.Linear.Example.UsageCheck Ty
  open WithPoSemiring poSemiring
  open WithInverses record
    { 0#⁻¹ = u0⁻¹ ; +⁻¹ = +⁻¹ ; 1#⁻¹ = u1⁻¹ ; *⁻¹ = *⁻¹; rep = rep }

  pattern ⊸I M = U.`con (`⊸I _ _ , ≡.refl , M)
  pattern !I M = U.`con (`!I _ _ , ≡.refl , ⟨ _ ⟩· M)
  pattern !E M N = U.`con (`!E _ _ _ , ≡.refl , M ✴⟨ _ ⟩ N)
  pattern ⊕I i M = U.`con (`⊕I i _ _ , ≡.refl , M)
  pattern ⊕E M N O = U.`con (`⊕E _ _ _ , ≡.refl , M ✴⟨ _ ⟩ (N , O))

  var# : ∀ {s} m {m< : True (m <? size s)} {d sz Γ} →
    U.[ d , ↑ sz ] U.ctx {s} _ Γ ⊢ Γ (#_ m {m<})
  var# {s} m {m<} = U.`var (U.lvar (#_ {s} m {m<}) ≡.refl _)

  cojoin-!ω : ∀ {A} → [ λR , ∞ ] []ᶜ ⊢ (! ω# A ⊸ ! ω# (! ω# A))
  cojoin-!ω = elab-unique _ (⊸I (!E (var# 0) (!I (!I (var# 1))))) []
