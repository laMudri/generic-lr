
{-# OPTIONS --sized-types --without-K --postfix-projections #-}

module Generic.Linear.Example.MuMuTilde.Term (Base : Set) where

  open import Algebra.Po
  open import Data.LTree
  open import Data.LTree.Automation
  open import Data.LTree.Vector
  open import Data.Product
  open import Level using (0ℓ)
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
  open import Relation.Unary.Bunched
  open import Size

  open import Generic.Linear.Example.ZeroOneMany
  open import Generic.Linear.Example.MuMuTilde poSemiring Base
  open import Generic.Linear.Everything Conc poSemiring
  open import Generic.Linear.Example.UsageCheck Conc
  open WithPoSemiring poSemiring
  open WithInverses record
    { 0#⁻¹ = u0⁻¹ ; +⁻¹ = +⁻¹ ; 1#⁻¹ = u1⁻¹ ; *⁻¹ = *⁻¹ ; rep = rep }




  pattern ucut v e = U.`con (`cut _ , ≡.refl , v ✴⟨ _ ⟩ e)
  pattern uμ c = U.`con (`μ _ , ≡.refl , c)
  pattern uμ∼ c = U.`con (`μ∼ _ , ≡.refl , c)
  pattern uλ e = U.`con (`λ _ , ≡.refl , e)
  pattern uλ∼ v = U.`con (`λ _ , ≡.refl , v)
  pattern u⟨_,_⟩ e f =
    U.`con (`⟨-,-⟩ _ _ , ≡.refl , (⟨ _ ⟩· e) ✴⟨ _ ⟩ (⟨ _ ⟩· f))
  pattern uμ⟨-,-⟩ c = U.`con (`μ⟨-,-⟩ _ _ , ≡.refl , c)





  myComm : (A B : Ty) → let 1A = 1# , A; 1B = 1# , B in
    [ MMT , ∞ ] []ᶜ ⊢ trm ((1# , (1A ⅋ 1B) ^⊥) ⅋ (1# , 1B ⅋ 1A))
  myComm A B = elab-unique MMT
    (uμ⟨-,-⟩ (ucut
      (uμ⟨-,-⟩ (ucut (uλ u⟨ uvar (# 3) , uvar (# 2) ⟩) (uvar (# 0))))
      (uvar (# 1))))
    []


