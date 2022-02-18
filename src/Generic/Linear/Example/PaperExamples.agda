
{-# OPTIONS --sized-types --without-K --postfix-projections #-}
module Generic.Linear.Example.PaperExamples where

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

module CPP0 (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ) where

  open PoSemiring poSemiring using () renaming (Carrier to Ann) public

  infixr 5 _⊸_
  infix 6 _⊕_




  data Ty : Set where
    ι : Ty
    _⊸_ _⊕_ : (A B : Ty) → Ty
    ! : (r : Ann) (A : Ty) → Ty




  open import Generic.Linear.Everything Ty poSemiring hiding (Ann) public




  data Side : Set where ll rr : Side





  data `λR : Set where
    `⊸I `⊸E : (A B : Ty) → `λR
    `⊕I : (i : Side) (A B : Ty) → `λR
    `⊕E : (A B C : Ty) → `λR
    `!I : (r : Ann) (A : Ty) → `λR
    `!E : (r : Ann) (A C : Ty) → `λR





  λR : System
  λR = `λR ▹ λ where
    (`⊸I A B)     → ⟨ [ 1# · A ]ᶜ `⊢ B ⟩                       =⇒ (A ⊸ B)
    (`⊸E A B)     → (⟨ []ᶜ `⊢ A ⊸ B ⟩ `✴ ⟨ []ᶜ `⊢ A ⟩)         =⇒ B
    (`!I r A)     → (r `· ⟨ []ᶜ `⊢ A ⟩)                        =⇒ (! r A)
    (`!E r A C)   → (⟨ []ᶜ `⊢ ! r A ⟩ `✴ ⟨ [ r · A ]ᶜ `⊢ C ⟩)  =⇒ C
    (`⊕I ll A B)  → ⟨ []ᶜ `⊢ A ⟩                               =⇒ (A ⊕ B)
    (`⊕I rr A B)  → ⟨ []ᶜ `⊢ B ⟩                               =⇒ (A ⊕ B)
    (`⊕E A B C)   →
      ⟨ []ᶜ `⊢ A ⊕ B ⟩ `✴ (⟨ [ 1# · A ]ᶜ `⊢ C ⟩ `∧ ⟨ [ 1# · B ]ᶜ `⊢ C ⟩) =⇒ C





  pattern ⊸I M = `con (`⊸I _ _ , ≡.refl , M)
  pattern !I sp M = `con (`!I _ _ , ≡.refl , ⟨ sp ⟩· M)
  pattern !E sp M N = `con (`!E _ _ _ , ≡.refl , M ✴⟨ sp ⟩ N)
  pattern ⊕I i M = `con (`⊕I i _ _ , ≡.refl , M)
  pattern ⊕E sp M N O = `con (`⊕E _ _ _ , ≡.refl , M ✴⟨ sp ⟩ (N , O))




  _ : Ann → Ty → Ty → Ty
  _ = λ r A B →



    (! r A) ⊸ B




module Example1 (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ) where

  open PoSemiring poSemiring
    renaming (Carrier to Ann
             ; _≤_ to _⊴_
             ; refl to ⊴-refl; trans to ⊴-trans
             )

  infixr 5 _·_⊸_
  infixr 6 _⊕_




  data Ty : Set where
    ι : Ty
    _·_⊸_ : (r : Ann) (A B : Ty) → Ty
    _⊕_ : (A B : Ty) → Ty




  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring
  open import Generic.Linear.Syntax.Term Ty rawPoSemiring




  data `Sys : Set where
    `lam `app : (r : Ann) (A B : Ty) → `Sys
    `inl `inr : (A B : Ty) → `Sys
    `case : (A B C : Ty) → `Sys




  Sys : System
  Sys .Label = `Sys



  Sys .rules (`lam r A B) =
    ⟨ [ r , A ]ᶜ `⊢ B ⟩
    =⇒ r · A ⊸ B
  Sys .rules (`app r A B) =
    ⟨ []ᶜ `⊢ r · A ⊸ B ⟩ `✴ r `· ⟨ []ᶜ `⊢ A ⟩
    =⇒ B




  Sys .rules (`inl A B) =
    ⟨ []ᶜ `⊢ A ⟩
    =⇒ A ⊕ B
  Sys .rules (`inr A B) =
    ⟨ []ᶜ `⊢ B ⟩
    =⇒ A ⊕ B
  Sys .rules (`case A B C) =
    ⟨ []ᶜ `⊢ A ⊕ B ⟩ `✴ (⟨ [ 1# , A ]ᶜ `⊢ C ⟩ `∧ ⟨ [ 1# , B ]ᶜ `⊢ C ⟩)
    =⇒ C


