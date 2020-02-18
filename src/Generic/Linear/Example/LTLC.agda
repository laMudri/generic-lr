module Generic.Linear.Example.LTLC where

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.Product
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Size

  infixr 5 _⊸_

  data Ty : Set where
    ι : Ty
    _⊸_ : (A B : Ty) → Ty

  data Ann : Set where
    u0 u1 uω : Ann

  open import Generic.Linear.Syntax Ty Ann

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

  open import Generic.Linear.Syntax.Term Ty Ann _⊴_ u0 _+_ u1 _*_
  open import Generic.Linear.Syntax.Interpretation Ty Ann _⊴_ u0 _+_ u1 _*_
    as Interp
  open import Generic.Linear.Thinning Ty Ann _⊴_ u0 _+_ u1 _*_

  data `LTLC : Set where
    `lam `app : (A B : Ty) → `LTLC

  LTLC : System
  LTLC = system `LTLC λ where
    (`lam A B) → rule (ctx [ u1 ] [ A ] `⊢ B) (A ⊸ B)
    (`app A B) → rule (([]ᶜ `⊢ (A ⊸ B)) `* ([]ᶜ `⊢ A)) B

  open Interp (Scope (Tm LTLC ∞)) hiding (_✴⟨_⟩_)

  Term = Tm LTLC ∞

  myC : (A B C : Ty) → Term ((A ⊸ B ⊸ C) ⊸ (B ⊸ A ⊸ C)) []ᶜ
  myC A B C =
    `con (`lam (A ⊸ B ⊸ C) (B ⊸ A ⊸ C) , refl ,  -- f
    `con (`lam B (A ⊸ C) , refl ,                -- b
    `con (`lam A C , refl ,                      -- a
    `con (`app B C , refl ,
      _✴⟨_⟩_
        {P = (([] ++ [ u1 ]) ++ [ u0 ]) ++ [ u1 ]}
        {Q = (([] ++ [ u0 ]) ++ [ u1 ]) ++ [ u0 ]}
        (`con (`app A (B ⊸ C) , refl , _✴⟨_⟩_
          {P = ((([] ++ [ u1 ]) ++ [ u0 ]) ++ [ u0 ]) ++ []}
          {Q = ((([] ++ [ u0 ]) ++ [ u0 ]) ++ [ u1 ]) ++ []}
          (`var (lvar
            (go-left (go-left (go-left (go-left (go-right here)))))
            refl
            (mk λ where
              (go-left (go-left (go-left (go-left (go-left (there () _))))))
              (go-left (go-left (go-left (go-left (go-right here))))) → ⊴-refl
              (go-left (go-left (go-left (go-right _)))) → ⊴-refl
              (go-left (go-left (go-right _))) → ⊴-refl
              (go-left (go-right (there () _)))
              (go-right (there () _))
            )))
          (mk λ where
            (go-left (go-left (go-left (go-left (there () _)))))
            (go-left (go-left (go-left (go-right _)))) → ⊴-refl
            (go-left (go-left (go-right _))) → ⊴-refl
            (go-left (go-right _)) → ⊴-refl
            (go-right (there () _))
          )
          (`var (lvar
            (go-left (go-left (go-right here)))
            refl
            (mk λ where
              (go-left (go-left (go-left (go-left (go-left (there () _))))))
              (go-left (go-left (go-left (go-left (go-right _))))) → ⊴-refl
              (go-left (go-left (go-left (go-right _)))) → ⊴-refl
              (go-left (go-left (go-right here))) → ⊴-refl
              (go-left (go-right (there () _)))
              (go-right (there () _))
            )))))
        (mk λ where
          (go-left (go-left (go-left (there () _))))
          (go-left (go-left (go-right _))) → ⊴-refl
          (go-left (go-right _)) → ⊴-refl
          (go-right _) → ⊴-refl
        )
        (`var (lvar
          (go-left (go-left (go-right here)))
          refl
          (mk λ where
            (go-left (go-left (go-left (go-left (there () _)))))
            (go-left (go-left (go-left (go-right _)))) → ⊴-refl
            (go-left (go-left (go-right here))) → ⊴-refl
            (go-left (go-right _)) → ⊴-refl
            (go-right (there () _))
          )))))))

  pattern var i les = `var (lvar i refl les)
  pattern lam t = `con (`lam _ _ , refl , t)
  pattern app A P Q sp s t =
    `con (`app A _ , refl , _✴⟨_⟩_ {P = P} {Q = Q} s sp t)
  pattern ↘ i = go-right i
  pattern ↙ i = go-left i

  myC′ : (A B C : Ty) → Term ((A ⊸ B ⊸ C) ⊸ (B ⊸ A ⊸ C)) []ᶜ
  myC′ A B C = lam (lam (lam
    (app B ((([] ++ [ u1 ]) ++ [ u0 ]) ++ [ u1 ])
           ((([] ++ [ u0 ]) ++ [ u1 ]) ++ [ u0 ])
           (mk λ where
             (↙ (↙ (↙ (there () _))))
             (↙ (↙ (↘ _))) → ⊴-refl
             (↙ (↘ _)) → ⊴-refl
             (↘ _) → ⊴-refl
           )
      (app A (((([] ++ [ u1 ]) ++ [ u0 ]) ++ [ u0 ]) ++ [])
             (((([] ++ [ u0 ]) ++ [ u0 ]) ++ [ u1 ]) ++ [])
             (mk λ where
               (↙ (↙ (↙ (↙ (there () _)))))
               (↙ (↙ (↙ (↘ _)))) → ⊴-refl
               (↙ (↙ (↘ _))) → ⊴-refl
               (↙ (↘ _)) → ⊴-refl
               (↘ (there () _))
             )
        (var (↙ (↙ (↙ (↙ (↘ here))))) (mk λ where
             (↙ (↙ (↙ (↙ (↙ (there () _))))))
             (↙ (↙ (↙ (↙ (↘ here))))) → ⊴-refl
             (↙ (↙ (↙ (↘ _)))) → ⊴-refl
             (↙ (↙ (↘ _))) → ⊴-refl
             (↙ (↘ (there () _)))
             (↘ (there () _))
        ))
        (var (↙ (↙ (↘ here))) (mk λ where
             (↙ (↙ (↙ (↙ (↙ (there () _))))))
             (↙ (↙ (↙ (↙ (↘ _))))) → ⊴-refl
             (↙ (↙ (↙ (↘ _)))) → ⊴-refl
             (↙ (↙ (↘ here))) → ⊴-refl
             (↙ (↘ (there () _)))
             (↘ (there () _))
        )))
      (var (↙ (↙ (↘ here))) (mk λ where
           (↙ (↙ (↙ (↙ (there () _)))))
           (↙ (↙ (↙ (↘ _)))) → ⊴-refl
           (↙ (↙ (↘ here))) → ⊴-refl
           (↙ (↘ _)) → ⊴-refl
           (↘ (there () _))
      )))))
