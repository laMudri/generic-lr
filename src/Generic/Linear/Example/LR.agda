module Generic.Linear.Example.LR where

  open import Algebra.Skew
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Automation
  open import Data.Product
  open import Level
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Relation.Unary.Bunched
  open import Size

  infixr 5 _⊸_

  data Dir : Set where
    syn chk : Dir

  open import Generic.Linear.Example.ZeroOneMany renaming (u01ω to Ann)

  data Ty : Set where
    ι : Ty
    _⊸_ : (A B : Ty) → Ty
    ! : (ρ : Ann) (A : Ty) → Ty

  Conc = Dir × Ty

  open import Generic.Linear.Syntax Conc Ann

  open import Generic.Linear.Syntax.Term Conc rawSkewSemiring
  open import Generic.Linear.Syntax.Interpretation Conc rawSkewSemiring
  open import Generic.Linear.Thinning Conc rawSkewSemiring

  data `LR : Set where
    `emb `ann : (A : Ty) → `LR
    `lam `app : (A B : Ty) → `LR
    `bang : (ρ : Ann) (A : Ty) → `LR
    `bm : (ρ : Ann) (A Z : Ty) → `LR

  LR : System
  LR = `LR ▹ λ where
    (`emb A) → ⟨ []ᶜ `⊢ (syn , A) ⟩ =⇒ (chk , A)
    (`ann A) → ⟨ []ᶜ `⊢ (chk , A) ⟩ =⇒ (syn , A)
    (`lam A B) → ⟨ ctx [ u1 ] [ syn , A ] `⊢ (chk , B) ⟩ =⇒ (chk , A ⊸ B)
    (`app A B) → ⟨ []ᶜ `⊢ (syn , A ⊸ B) ⟩ `✴ ⟨ []ᶜ `⊢ (chk , A) ⟩ =⇒ (syn , B)
    (`bang ρ A) → ρ `· ⟨ []ᶜ `⊢ (chk , A) ⟩ =⇒ (chk , ! ρ A)
    (`bm ρ A Z) →
      ⟨ []ᶜ `⊢ (syn , ! ρ A) ⟩ `✴ ⟨ ctx [ ρ ] [ syn , A ] `⊢ (chk , Z) ⟩
      =⇒ (syn , Z)

  Term = Tm LR ∞

  pattern var i les = `var (lvar i refl les)
  pattern emb e = `con (`emb _ , refl , e)
  pattern ann S s = `con (`ann S , refl , s)
  pattern lam t = `con (`lam _ _ , refl , t)
  pattern app P Q sp f s =
    `con (`app _ _ , refl , _✴⟨_⟩_ {y = P} {z = Q} f sp s)
  pattern bang P sp s = `con (`bang _ _ , refl , ⟨_⟩·_ {z = P} sp s)
  pattern bm T P Q sp e t =
    `con (`bm _ _ T , refl , _✴⟨_⟩_ {y = P} {z = Q} e sp t)

  open import Generic.Linear.Example.UsageCheck Conc
  open WithSkewSemiring skewSemiring
  open WithInverses u0⁻¹ +⁻¹ u1⁻¹ *⁻¹ rep

  module V where

    open import Generic.Linear.Syntax.Term Conc U.0-rawSkewSemiring public
    open import Generic.Linear.Syntax.Interpretation Conc U.0-rawSkewSemiring
      public
    open import Generic.Linear.Thinning Conc U.0-rawSkewSemiring public

  pattern uvar i = V.`var (V.lvar i refl _)
  pattern uemb e = V.`con (`emb _ , refl , e)
  pattern uann S s = V.`con (`ann S , refl , s)
  pattern ulam t = V.`con (`lam _ _ , refl , t)
  pattern uapp f s = V.`con (`app _ _ , refl , f ✴⟨ _ ⟩ s)
  pattern ubang s = V.`con (`bang _ _ , refl , ⟨ _ ⟩· s)
  pattern ubm T e t = V.`con (`bm _ _ T , refl , e ✴⟨ _ ⟩ t)

  myK : ∀ A B → Term _ []ᶜ
  myK A B = elab-unique LR
    (uann (! uω (A ⊸ B) ⊸ ! uω A ⊸ ! uω B)
          (ulam (ulam (uemb (ubm _ (uvar (# 0)) (uemb (ubm _ (uvar (# 1))
            (ubang (uemb (uapp (uvar (# 2)) (uemb (uvar (# 3)))))))))))))
    []

  {-
  myK : ∀ A B → Term _ []ᶜ
  myK A B =
    ann (! uω (A ⊸ B) ⊸ ! uω A ⊸ ! uω B)
        (lam (lam (emb (bm _
          (((([] ++ []) ++ [ u1 ]) ++ [ u0 ]) ++ [])
          (((([] ++ []) ++ [ u0 ]) ++ [ u1 ]) ++ [])
          (((([]₂ ++₂ []₂) ++₂ [ ⊴-refl ]₂) ++₂ [ ⊴-refl ]₂) ++₂ []₂)
          (var (↙ (↙ (↙ (↘ here))))
               ((((([]₂ ++₂ []₂) ++₂ [ ⊴-refl ]₂) ++₂ [ ⊴-refl ]₂) ++₂ []₂)
                 ++₂ []₂))
          (emb (bm _
            (((((([] ++ []) ++ [ u0 ]) ++ [ u1 ]) ++ []) ++ [ uω ]) ++ [])
            (((((([] ++ []) ++ [ u0 ]) ++ [ u0 ]) ++ []) ++ [ uω ]) ++ [])
            (((((([]₂ ++₂ []₂) ++₂ [ ⊴-refl ]₂) ++₂ [ ⊴-refl ]₂) ++₂ []₂) ++₂
              [ ⊴-refl ]₂) ++₂ []₂)
            (var (↙ (↙ (↙ (↙ (↘ here)))))
                 ((((((([]₂ ++₂ []₂) ++₂ [ ⊴-refl ]₂) ++₂ [ ⊴-refl ]₂) ++₂ []₂)
                   ++₂ [ ω⊴0 ]₂) ++₂ []₂) ++₂ []₂))
            (bang
              ((((((([] ++ []) ++ [ u0 ]) ++ [ u0 ]) ++ [])
                ++ [ uω ]) ++ []) ++ [ uω ])
              ((((((([]₂ ++₂ []₂) ++₂ [ ⊴-refl ]₂) ++₂ [ ⊴-refl ]₂) ++₂ []₂)
                ++₂ [ ⊴-refl ]₂) ++₂ []₂) ++₂ [ ⊴-refl ]₂)
              (emb (app
                ((((((((([] ++ []) ++ [ u0 ]) ++ [ u0 ]) ++ [])
                  ++ [ uω ]) ++ []) ++ [ uω ]) ++ []) ++ [])
                ((((((((([] ++ []) ++ [ u0 ]) ++ [ u0 ]) ++ [])
                  ++ [ uω ]) ++ []) ++ [ uω ]) ++ []) ++ [])
                ((((((((([]₂ ++₂ []₂) ++₂ [ ⊴-refl ]₂) ++₂ [ ⊴-refl ]₂) ++₂ []₂)
                  ++₂ [ ⊴-refl ]₂) ++₂ []₂) ++₂ [ ⊴-refl ]₂) ++₂ []₂) ++₂ []₂)
                (var (↙ (↙ (↙ (↙ (↙ (↘ here))))))
                     (((((((((([]₂ ++₂ []₂) ++₂ [ ⊴-refl ]₂) ++₂ [ ⊴-refl ]₂)
                       ++₂ []₂) ++₂ [ ω⊴1 ]₂) ++₂ []₂) ++₂ [ ω⊴0 ]₂) ++₂ []₂)
                       ++₂ []₂) ++₂ []₂))
                (emb (var
                  (↙ (↙ (↙ (↙ (↘ here)))))
                  ((((((((((([]₂ ++₂ []₂) ++₂ [ ⊴-refl ]₂) ++₂ [ ⊴-refl ]₂)
                    ++₂ []₂) ++₂ [ ω⊴0 ]₂) ++₂ []₂) ++₂ [ ω⊴1 ]₂) ++₂ []₂)
                    ++₂ []₂) ++₂ []₂) ++₂ []₂))))))))))))
  -}
