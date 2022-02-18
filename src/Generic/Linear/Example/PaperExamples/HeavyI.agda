
{-# OPTIONS --sized-types --without-K --postfix-projections #-}

open import Algebra.Po
open import Level

module Generic.Linear.Example.PaperExamples.HeavyI
  (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

open import Algebra.Po.Construct.Nat
open import Data.LTree
open import Data.LTree.Vector
open import Data.Product
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Unary.Bunched
open import Size

open import Generic.Linear.Example.PaperExamples
open CPP0 poSemiring




test : ∀ r A B → [ λR , ∞ ] []ᶜ ⊢ (! r (A ⊕ B) ⊸ ! r (B ⊕ A))
test r A B =
  let prf0 : 0# ≤ r * 0#; prf0 = ≤-reflexive (sym (annihilʳ _)) in
  let prf1 : r ≤ r * 1#; prf1 = ≤-reflexive (sym (*-identityʳ _)) in
  let prf2 = (≤*-refl ++ₙ [ ≤-refl ]ₙ) ++ₙ []ₙ in
  ⊸I (!E (+*-identity↘ _)
    (`var (lvar (↙ (↘ here)) ≡.refl (([]ₙ ++ₙ [ ≤-refl ]ₙ) ++ₙ []ₙ)))
    (!I (([]ₙ ++ₙ [ prf0 ]ₙ) ++ₙ [ prf1 ]ₙ)
      (⊕E (+*-identity↘ _ ++ₙ []ₙ)
        (`var (lvar (↙ (↙ (↘ here))) ≡.refl (≤*-refl ++ₙ []ₙ)))
        (⊕I rr (`var (lvar (↙ (↘ here)) ≡.refl prf2)))
        (⊕I ll (`var (lvar (↙ (↘ here)) ≡.refl prf2))))))


