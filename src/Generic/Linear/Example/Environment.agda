{-# OPTIONS --sized-types --without-K --postfix-projections #-}
module Generic.Linear.Example.Environment where

open import Algebra.Po
open import Algebra.Po.Construct.Nat
open import Data.LTree
open import Data.LTree.Automation
open import Data.LTree.Vector
open import Data.Product
open import Data.Unit using (⊤; tt)
open import Function.Base using (_$_)
open import Level
open import Relation.Binary.PropositionalEquality as ≡ hiding ([_])
open import Relation.Unary.Bunched
open import Size

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Nat.Properties using (+-*-isSemiring)
open import Function.Base using (const)

ℕ≡-poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ
ℕ≡-poSemiring = record
  { Carrier = ℕ
  ; _≈_ = _≡_
  ; _≤_ = _≡_
  ; 0# = 0
  ; _+_ = _+_
  ; 1# = 1
  ; _*_ = _*_
  ; isPoSemiring = record
    { isPartialOrder = record { isPreorder = isPreorder ; antisym = const }
    ; isSemiring = +-*-isSemiring
    ; +-mono = cong₂ _+_
    ; *-mono = cong₂ _*_
    }
  }
open PoSemiring ℕ≡-poSemiring using (+-inter; annihilʳ; distribʳ) renaming
  (rawPoSemiring to ℕ≡-rawPoSemiring)

module Example0 where

  data Ty : Set where
    A B C D : Ty

  open import Generic.Linear.Variable Ty ℕ≡-rawPoSemiring
  open import Generic.Linear.Syntax Ty ℕ
  open import Generic.Linear.Environment Ty ℕ≡-poSemiring

  open import Algebra.Relational
  open import Algebra.Relational.Relation
  open RelLeftSemimoduleFuncRel

  square : ∀ {A : Set} {a b a′ b′ : A} → a′ ≡ a → b ≡ b′ → a ≡ b → a′ ≡ b′
  square refl refl q = q

  ρ : [ _∋_ ]
    ([ 6 · A ]ᶜ ++ᶜ [ 0 · B ]ᶜ) ++ᶜ ([ 1 · C ]ᶜ ++ᶜ [ 0 · D ]ᶜ) ⇒ᵉ
    ([ 1 · C ]ᶜ ++ᶜ ([ 2 · A ]ᶜ ++ᶜ [ 4 · A ]ᶜ))
  ρ .Ψ .rel u v =
    v (↙ (↙ here)) ≡ u (↘ (↙ here)) + u (↘ (↘ here)) ×
    v (↙ (↘ here)) ≡ 0 ×
    v (↘ (↙ here)) ≡ u (↙ here) ×
    v (↘ (↘ here)) ≡ 0
  ρ .Ψ .rel-≤ₘ uu vv (a , b , c , d) =
    trans (vv .get _) (trans a (cong₂ _+_ (uu .get _) (uu .get _))) ,
    trans (vv .get _) b ,
    trans (vv .get _) (trans c (uu .get _)) ,
    trans (vv .get _) d
  ρ .Ψ .rel-0ₘ (sp0 , (a , b , c , d)) = λ where
    .get (↙ (↙ here)) → trans a (cong₂ _+_ (sp0 .get _) (sp0 .get _))
    .get (↙ (↘ here)) → b
    .get (↘ (↙ here)) → trans c (sp0 .get _)
    .get (↘ (↘ here)) → d
  ρ .Ψ .rel-+ₘ {x} {y} (sp+ , (a , b , c , d)) = _↘,_,↙_
    {left = ([ _ ] ++ [ _ ]) ++ ([ _ ] ++ [ _ ])}
    {right = ([ _ ] ++ [ _ ]) ++ ([ _ ] ++ [ _ ])}
    (refl , refl , refl , refl)
    (λ where
      .get (↙ (↙ here)) →
        trans a
          (trans
            (cong₂ _+_ (sp+ .get (↘ (↙ here))) (sp+ .get (↘ (↘ here))))
            (+-inter (x (↘ (↙ here))) _ _ _))
      .get (↙ (↘ here)) → b
      .get (↘ (↙ here)) → trans c (sp+ .get _)
      .get (↘ (↘ here)) → d
        )
    (refl , refl , refl , refl)
  ρ .Ψ .rel-*ₘ {r} (sp* , (a , b , c , d)) = _,_
    {middle = ([ _ ] ++ [ _ ]) ++ ([ _ ] ++ [ _ ])}
    (refl , refl , refl , refl)
    λ where
      .get (↙ (↙ here)) →
        trans a
          (trans
            (cong₂ _+_ (sp* .get (↘ (↙ here))) (sp* .get (↘ (↘ here))))
            (sym (distribʳ r _ _)))
      .get (↙ (↘ here)) → trans b (sym (annihilʳ r))
      .get (↘ (↙ here)) → trans c (sp* .get _)
      .get (↘ (↘ here)) → trans d (sym (annihilʳ r))
  ρ .Ψ .func u = _,_
    {witness = ([ _ ] ++ [ _ ]) ++ ([ _ ] ++ [ _ ])}
    (refl , refl , refl , refl)
    λ {z} (a , b , c , d) → λ where
      .get (↙ (↙ here)) → a
      .get (↙ (↘ here)) → b
      .get (↘ (↙ here)) → c
      .get (↘ (↘ here)) → d
  ρ .fit-here = refl , refl , refl , refl
  ρ .lookup (a , b , c , d) (lvar (↙ here) q bs) =
    lvar (↘ (↙ here)) q λ where
      .get (↙ (↙ here)) →
        trans a (cong₂ _+_ (bs .get (↘ (↙ here))) (bs .get (↘ (↘ here))))
      .get (↙ (↘ here)) → b
      .get (↘ (↙ here)) → trans c (bs .get _)
      .get (↘ (↘ here)) → d
  ρ .lookup (a , b , c , d) (lvar (↘ (↙ here)) q bs) =
    lvar (↙ (↙ here)) q λ where
      .get (↙ (↙ here)) →
        trans a (cong₂ _+_ (bs .get (↘ (↙ here))) (bs .get (↘ (↘ here))))
      .get (↙ (↘ here)) → b
      .get (↘ (↙ here)) → trans c (bs .get _)
      .get (↘ (↘ here)) → d
  ρ .lookup (a , b , c , d) (lvar (↘ (↘ here)) q bs) =
    lvar (↙ (↙ here)) q λ where
      .get (↙ (↙ here)) →
        trans a (cong₂ _+_ (bs .get (↘ (↙ here))) (bs .get (↘ (↘ here))))
      .get (↙ (↘ here)) → b
      .get (↘ (↙ here)) → trans c (bs .get _)
      .get (↘ (↘ here)) → d

module Example1 where

  open import Generic.Linear.Example.PaperExamples using (module CPP0)
  open CPP0 ℕ≡-poSemiring

  open With-psh^𝓥 {𝓥 = [ λR , ∞ ]_⊢_} psh^⊢

  σ : (A B C : Ty) → [ [ λR , ∞ ]_⊢_ ]
    ([ 0 · A ]ᶜ ++ᶜ ([ 2 · B ⊸ C ]ᶜ ++ᶜ [ 3 · B ]ᶜ)) ⇒ᵉ
    ([ 1 · B ]ᶜ ++ᶜ [ 2 · C ]ᶜ)
  σ A B C = ++ᵉ $ _✴⟨_⟩_
    {y = [ 0 ] ++ ([ 0 ] ++ [ 1 ])} {[ 0 ] ++ ([ 2 ] ++ [ 2 ])}
    ([-]ᵉ (⟨_⟩·_
      {z = [ 0 ] ++ ([ 0 ] ++ [ 1 ])}
      ([ ≡.refl ]ₙ ++ₙ ([ ≡.refl ]ₙ ++ₙ [ ≡.refl ]ₙ))
      (`var (lvar (# 2) ≡.refl
        ([ ≡.refl ]ₙ ++ₙ ([ ≡.refl ]ₙ ++ₙ [ ≡.refl ]ₙ))))))
    ([ ≡.refl ]ₙ ++ₙ ([ ≡.refl ]ₙ ++ₙ [ ≡.refl ]ₙ))
    ([-]ᵉ (⟨_⟩·_
      {z = [ 0 ] ++ ([ 1 ] ++ [ 1 ])}
      ([ ≡.refl ]ₙ ++ₙ ([ ≡.refl ]ₙ ++ₙ [ ≡.refl ]ₙ))
      (⊸E ([ ≡.refl ]ₙ ++ₙ ([ ≡.refl ]ₙ ++ₙ [ ≡.refl ]ₙ))
        (`var (lvar
          {Γ = ctx (([ 0 ] ++ ([ 1 ] ++ [ 0 ])) ++ []) _}
          (# 1) ≡.refl
          (([ ≡.refl ]ₙ ++ₙ ([ ≡.refl ]ₙ ++ₙ [ ≡.refl ]ₙ)) ++ₙ []ₙ)))
        (`var (lvar
          {Γ = ctx (([ 0 ] ++ ([ 0 ] ++ [ 1 ])) ++ []) _}
          (# 2) ≡.refl
          (([ ≡.refl ]ₙ ++ₙ ([ ≡.refl ]ₙ ++ₙ [ ≡.refl ]ₙ)) ++ₙ []ₙ))))))
