module Generic.Linear.Example.LR where

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.Product
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Size

  infixr 5 _⊸_

  data Dir : Set where
    syn chk : Dir

  data Ann : Set where
    u0 u1 uω : Ann

  data Ty : Set where
    ι : Ty
    _⊸_ : (A B : Ty) → Ty
    ! : (ρ : Ann) (A : Ty) → Ty

  Conc = Dir × Ty

  open import Generic.Linear.Syntax Conc Ann

  data _⊴_ : (a b : Ann) → Set where
    ⊴-refl : ∀ {a} → a ⊴ a
    ω⊴0 : uω ⊴ u0
    ω⊴1 : uω ⊴ u1

  _+_ : (a b : Ann) → Ann
  u0 + b = b
  u1 + u0 = u1
  u1 + u1 = uω
  u1 + uω = uω
  uω + b = uω

  _*_ : (a b : Ann) → Ann
  u0 * b = u0
  u1 * b = u1
  uω * u0 = u0
  uω * u1 = uω
  uω * uω = uω

  open import Generic.Linear.Syntax.Term Conc Ann _⊴_ u0 _+_ u1 _*_
  open import Generic.Linear.Syntax.Interpretation Conc Ann _⊴_ u0 _+_ u1 _*_
  open import Generic.Linear.Thinning Conc Ann _⊴_ u0 _+_ u1 _*_

  data `LR : Set where
    `emb `ann : (A : Ty) → `LR
    `lam `app : (A B : Ty) → `LR
    `bang : (ρ : Ann) (A : Ty) → `LR
    `bm : (ρ : Ann) (A Z : Ty) → `LR

  LR : System
  LR = system `LR λ where
    (`emb A) → rule ([]ᶜ `⊢ (syn , A))
                    (chk , A)
    (`ann A) → rule ([]ᶜ `⊢ (chk , A))
                    (syn , A)
    (`lam A B) → rule (ctx [ u1 ] [ syn , A ] `⊢ (chk , B))
                      (chk , A ⊸ B)
    (`app A B) → rule (([]ᶜ `⊢ (syn , A ⊸ B)) `* ([]ᶜ `⊢ (chk , A)))
                      (syn , B)
    (`bang ρ A) → rule (ρ `· ([]ᶜ `⊢ (chk , A)))
                       (chk , ! ρ A)
    (`bm ρ A Z) → rule (([]ᶜ `⊢ (syn , ! ρ A))
                        `* (ctx [ ρ ] [ syn , A ] `⊢ (chk , Z)))
                       (syn , Z)

  open WithScope (Scope (Tm LR ∞))

  Term = Tm LR ∞

  pattern var i les = `var (lvar i refl les)
  pattern emb e = `con (`emb _ , refl , e)
  pattern ann S s = `con (`ann S , refl , s)
  pattern lam t = `con (`lam _ _ , refl , t)
  pattern app P Q sp f s =
    `con (`app _ _ , refl , _✴⟨_⟩_ {P = P} {Q = Q} f sp s)
  pattern bang P sp s = `con (`bang _ _ , refl , ⟨_⟩·_ {P = P} sp s)
  pattern bm T P Q sp e t =
    `con (`bm _ _ T , refl , _✴⟨_⟩_ {P = P} {Q = Q} e sp t)

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
