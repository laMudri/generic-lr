{-# OPTIONS --sized-types --without-K --postfix-projections --prop #-}

module Generic.Linear.Example.LRBidi where

  open import Algebra.Po
  open import Data.Bool
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Automation
  open import Data.Product
  open import Data.Unit
  open import Level
  open import Proposition
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Relation.Unary.Bunched
  open import Size

  data Dir : Set where
    syn chk : Dir

  open import Generic.Linear.Example.LLFlags
  open import Generic.Linear.Example.ZeroOneMany renaming (u01ω to Ann)

  module WithLLFlags (llfl : LLFlags) where

    open LLFlags llfl

    infixr 5 _⊸_

    data Ty : Set where
      ι : Ty
      _⊸_ : {{_ : Has-⊸}} (A B : Ty) → Ty
      ! : {{_ : Has-!}} (ρ : Ann) (A : Ty) → Ty
      nat : {{_ : Has-ℕ}} → Ty

    Conc = Dir × Ty

    open import Generic.Linear.Syntax Conc Ann public

    open import Generic.Linear.Syntax.Term Conc rawPoSemiring
    open import Generic.Linear.Syntax.Interpretation Conc rawPoSemiring
    open import Generic.Linear.Variable Conc rawPoSemiring
    open import Generic.Linear.Renaming Conc poSemiring

    data `LR : Set where
      `emb `ann : (A : Ty) → `LR
      `lam `app : {{_ : Has-⊸}} (A B : Ty) → `LR
      `bang : {{_ : Has-!}} (ρ : Ann) (A : Ty) → `LR
      `bm : {{_ : Has-!}} (ρ : Ann) (A Z : Ty) → `LR
      `ze `su : {{_ : Has-ℕ}} → `LR
      `iter : {{_ : Has-ℕ}} (Z : Ty) → `LR

    flags : PremisesFlags
    flags = record noPremisesFlags
      { Has-∧ = ⊤ᴾ; Has-ℑ = ⊤ᴾ; Has-✴ = ⊤ᴾ; Has-· = ⊤ᴾ; Has-□ = ⊤ᴾ }

    LR : System flags
    LR = `LR ▹ λ where
      (`emb A) → ⟨ []ᶜ `⊢ (syn , A) ⟩ `⊆ (chk , A)
      (`ann A) → ⟨ []ᶜ `⊢ (chk , A) ⟩ `⊆ (syn , A)
      (`lam A B) → ⟨ [ u1 , syn , A ]ᶜ `⊢ (chk , B) ⟩ `⊆ (chk , A ⊸ B)
      (`app A B) → ⟨ []ᶜ `⊢ (syn , A ⊸ B) ⟩ `✴ ⟨ []ᶜ `⊢ (chk , A) ⟩ `⊆ (syn , B)
      (`bang ρ A) → ρ `· ⟨ []ᶜ `⊢ (chk , A) ⟩ `⊆ (chk , ! ρ A)
      (`bm ρ A Z) →
        ⟨ []ᶜ `⊢ (syn , ! ρ A) ⟩ `✴ ⟨ [ ρ , syn , A ]ᶜ `⊢ (chk , Z) ⟩
        `⊆ (syn , Z)
      `ze → `ℑ `⊆ (chk , nat)
      `su → ⟨ []ᶜ `⊢ (chk , nat) ⟩ `⊆ (chk , nat)
      (`iter Z) →
        ⟨ []ᶜ `⊢ (syn , nat) ⟩ `✴
        `□⁰⁺ (⟨ []ᶜ `⊢ (chk , Z) ⟩ `∧ ⟨ [ u1 , syn , Z ]ᶜ `⊢ (chk , Z) ⟩)
        `⊆ (syn , Z)

    Term = [ LR , ∞ ]_⊢_

    pattern var i les = `var (lvar i refl les)
    pattern emb e = `con (`emb _ , refl , e)
    pattern ann S s = `con (`ann S , refl , s)
    pattern lam t = `con (`lam _ _ , refl , t)
    pattern app P Q sp f s =
      `con (`app _ _ , refl , _✴⟨_⟩_ {y = P} {z = Q} f sp s)
    pattern bang P sp s = `con (`bang _ _ , refl , ⟨_⟩·_ {z = P} sp s)
    pattern bm T P Q sp e t =
      `con (`bm _ _ T , refl , _✴⟨_⟩_ {y = P} {z = Q} e sp t)

    open import Generic.Linear.Example.UsageCheck Conc public
    open WithPoSemiring poSemiring public
    open WithInverses flags record
      { 0#⁻¹ = u0⁻¹ ; +⁻¹ = +⁻¹ ; 1#⁻¹ = u1⁻¹ ; *⁻¹ = *⁻¹ ; rep = rep }
      public

    module V where

      open import Generic.Linear.Syntax.Term Conc U.0-rawPoSemiring public
      open import Generic.Linear.Syntax.Interpretation Conc U.0-rawPoSemiring
        public
      open import Generic.Linear.Variable Conc U.0-rawPoSemiring public
      open import Generic.Linear.Renaming Conc U.0-poSemiring public

    pattern uvar i = V.`var (V.lvar i refl _)
    pattern uemb e = V.`con (`emb _ , refl , e)
    pattern uann S s = V.`con (`ann S , refl , s)
    pattern ulam t = V.`con (`lam _ _ , refl , t)
    pattern uapp f s = V.`con (`app _ _ , refl , f ✴⟨ _ ⟩ s)
    pattern ubang s = V.`con (`bang _ _ , refl , ⟨ _ ⟩· s)
    pattern ubm T e t = V.`con (`bm _ _ T , refl , e ✴⟨ _ ⟩ t)
    pattern uze = V.`con (`ze , refl , ℑ⟨ _ ⟩)
    pattern usu s = V.`con (`su , refl , s)
    pattern uiter T e s t =
      V.`con (`iter T , refl , e ✴⟨ _ ⟩ (□⟨ _ , _ , _ , _ ⟩ (s , t)))

  open WithLLFlags allLLFlags

  myK : ∀ A B → Term []ᶜ _
  myK A B = elab-unique LR
    (uann (! uω (A ⊸ B) ⊸ ! uω A ⊸ ! uω B)
          (ulam (ulam (uemb (ubm _ (uvar (# 0)) (uemb (ubm _ (uvar (# 1))
            (ubang (uemb (uapp (uvar (# 2)) (uemb (uvar (# 3)))))))))))))
    []

  deepid : Term []ᶜ _
  deepid = elab-unique LR
    (uann (nat ⊸ nat)
          (ulam (uemb (uiter _ (uvar (# 0))
            uze
            (usu (uemb (uvar (# 1))))))))
    []

  -- dupNat : nat ⊸ ! uω nat
  -- dupNat = λn. iter n return ! uω nat where
  --   0          ↦ bang 0
  --   suc _ | ih ↦ let bang m = ih return ! uω nat in
  --                bang (suc m)

  dupNat : Term []ᶜ (syn , nat ⊸ ! uω nat)
  dupNat = elab-unique LR
    (uann (nat ⊸ ! uω nat)
          (ulam (uemb
            (uiter (! uω nat) (uvar (# 0))
              (ubang uze)
              (uemb (ubm (! uω nat) (uvar (# 1))
                (ubang (usu (uemb (uvar (# 2)))))))))))
    []

  {-
  myK : ∀ A B → Term []ᶜ _
  myK A B =
    ann (! uω (A ⊸ B) ⊸ ! uω A ⊸ ! uω B)
        (lam (lam (emb (bm _
          (((([] ++ []) ++ [ u1 ]) ++ [ u0 ]) ++ [])
          (((([] ++ []) ++ [ u0 ]) ++ [ u1 ]) ++ [])
          (((([]₂ ++₂ []₂) ++₂ [ ≤-refl ]₂) ++₂ [ ≤-refl ]₂) ++₂ []₂)
          (var (↙ (↙ (↙ (↘ here))))
               ((((([]₂ ++₂ []₂) ++₂ [ ≤-refl ]₂) ++₂ [ ≤-refl ]₂) ++₂ []₂)
                 ++₂ []₂))
          (emb (bm _
            (((((([] ++ []) ++ [ u0 ]) ++ [ u1 ]) ++ []) ++ [ uω ]) ++ [])
            (((((([] ++ []) ++ [ u0 ]) ++ [ u0 ]) ++ []) ++ [ uω ]) ++ [])
            (((((([]₂ ++₂ []₂) ++₂ [ ≤-refl ]₂) ++₂ [ ≤-refl ]₂) ++₂ []₂) ++₂
              [ ≤-refl ]₂) ++₂ []₂)
            (var (↙ (↙ (↙ (↙ (↘ here)))))
                 ((((((([]₂ ++₂ []₂) ++₂ [ ≤-refl ]₂) ++₂ [ ≤-refl ]₂) ++₂ []₂)
                   ++₂ [ ω≤0 ]₂) ++₂ []₂) ++₂ []₂))
            (bang
              ((((((([] ++ []) ++ [ u0 ]) ++ [ u0 ]) ++ [])
                ++ [ uω ]) ++ []) ++ [ uω ])
              ((((((([]₂ ++₂ []₂) ++₂ [ ≤-refl ]₂) ++₂ [ ≤-refl ]₂) ++₂ []₂)
                ++₂ [ ≤-refl ]₂) ++₂ []₂) ++₂ [ ≤-refl ]₂)
              (emb (app
                ((((((((([] ++ []) ++ [ u0 ]) ++ [ u0 ]) ++ [])
                  ++ [ uω ]) ++ []) ++ [ uω ]) ++ []) ++ [])
                ((((((((([] ++ []) ++ [ u0 ]) ++ [ u0 ]) ++ [])
                  ++ [ uω ]) ++ []) ++ [ uω ]) ++ []) ++ [])
                ((((((((([]₂ ++₂ []₂) ++₂ [ ≤-refl ]₂) ++₂ [ ≤-refl ]₂) ++₂ []₂)
                  ++₂ [ ≤-refl ]₂) ++₂ []₂) ++₂ [ ≤-refl ]₂) ++₂ []₂) ++₂ []₂)
                (var (↙ (↙ (↙ (↙ (↙ (↘ here))))))
                     (((((((((([]₂ ++₂ []₂) ++₂ [ ≤-refl ]₂) ++₂ [ ≤-refl ]₂)
                       ++₂ []₂) ++₂ [ ω≤1 ]₂) ++₂ []₂) ++₂ [ ω≤0 ]₂) ++₂ []₂)
                       ++₂ []₂) ++₂ []₂))
                (emb (var
                  (↙ (↙ (↙ (↙ (↘ here)))))
                  ((((((((((([]₂ ++₂ []₂) ++₂ [ ≤-refl ]₂) ++₂ [ ≤-refl ]₂)
                    ++₂ []₂) ++₂ [ ω≤0 ]₂) ++₂ []₂) ++₂ [ ω≤1 ]₂) ++₂ []₂)
                    ++₂ []₂) ++₂ []₂) ++₂ []₂))))))))))))
  -}
