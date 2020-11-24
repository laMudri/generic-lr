{-# OPTIONS --safe --sized-types --without-K --postfix-projections #-}

module Generic.Linear.Example.LTLC where

  open import Algebra.Skew
  open import Data.Empty
  open import Data.List as L using (List; _∷_) renaming ([] to []L)
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.Product
  open import Data.Unit
  open import Function.Base
  open import Level
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
  open import Relation.Unary.Bunched
  open import Size

  infixr 5 _⊸_

  open import Generic.Linear.Example.ZeroOneMany renaming (u01ω to Ann)

  data Ty : Set where
    ι : Ty
    _⊸_ : (A B : Ty) → Ty

  open import Generic.Linear.Syntax Ty Ann

  open import Generic.Linear.Syntax.Term Ty rawSkewSemiring
  open import Generic.Linear.Syntax.Interpretation Ty rawSkewSemiring
  open import Generic.Linear.Thinning Ty rawSkewSemiring

  data `LTLC : Set where
    `lam `app : (A B : Ty) → `LTLC

  LTLC : System
  LTLC = system `LTLC λ where
    (`lam A B) → rule ([(u1 , A)]ᶜ `⊢ B) (A ⊸ B)
    (`app A B) → rule (([]ᶜ `⊢ (A ⊸ B)) `* ([]ᶜ `⊢ A)) B

  open WithScope (Scope (Tm LTLC ∞))

  Term = Tm LTLC ∞

  pattern var i les = `var (lvar i refl les)
  pattern lam t = `con (`lam _ _ , refl , t)
  pattern app A P Q sp s t =
    `con (`app A _ , refl , _✴⟨_⟩_ {y = P} {z = Q} s sp t)

  open import Generic.Linear.Example.UsageCheck Ty
  open WithSkewSemiring skewSemiring
  open WithInverses u0⁻¹ +⁻¹ u1⁻¹ *⁻¹

  module V where

    open import Generic.Linear.Syntax.Term Ty U.0-rawSkewSemiring public
    open import Generic.Linear.Syntax.Interpretation Ty U.0-rawSkewSemiring
      public
    open import Generic.Linear.Thinning Ty U.0-rawSkewSemiring public

  pattern uvar i = V.`var (V.lvar i refl _)
  pattern ulam t = V.`con (`lam _ _ , refl , t)
  pattern uapp s t =
    V.`con (`app _ _ , refl , s ✴⟨ _ ⟩ t)

  myC : (A B C : Ty) → Term ((A ⊸ B ⊸ C) ⊸ (B ⊸ A ⊸ C)) []ᶜ
  myC A B C = elab-unique LTLC
    (ulam (ulam (ulam
      (uapp (uapp (uvar (↙ (↙ (↙ (↙ (↘ here))))))
                  (uvar (↙ (↙ (↘ here)))))
            (uvar (↙ (↙ (↘ here))))))))
    []

  myB : (A B C : Ty) → Term ((B ⊸ C) ⊸ (A ⊸ B) ⊸ (A ⊸ C)) []ᶜ
  myB A B C = elab-unique LTLC
    (ulam (ulam (ulam
      (uapp (uvar (↙ (↙ (↙ (↘ here)))))
        (uapp (uvar (↙ (↙ (↙ (↘ here))))) (uvar (↙ (↙ (↘ here)))))))))
    []

  {- Commenting out old stuff because it takes forever to check.
  myC : (A B C : Ty) → Term ((A ⊸ B ⊸ C) ⊸ (B ⊸ A ⊸ C)) []ᶜ
  myC A B C =
    `con (`lam (A ⊸ B ⊸ C) (B ⊸ A ⊸ C) , refl ,  -- f
    `con (`lam B (A ⊸ C) , refl ,                -- b
    `con (`lam A C , refl ,                      -- a
    `con (`app B C , refl ,
      _✴⟨_⟩_
        {y = (([] ++ [ u1 ]) ++ [ u0 ]) ++ [ u1 ]}
        {z = (([] ++ [ u0 ]) ++ [ u1 ]) ++ [ u0 ]}
        (`con (`app A (B ⊸ C) , refl , _✴⟨_⟩_
          {y = ((([] ++ [ u1 ]) ++ [ u0 ]) ++ [ u0 ]) ++ []}
          {z = ((([] ++ [ u0 ]) ++ [ u0 ]) ++ [ u1 ]) ++ []}
          (`var (lvar
            (↙ (↙ (↙ (↙ (↘ here)))))
            refl
            (mk λ where
              (↙ (↙ (↙ (↙ (↙ (there () _))))))
              (↙ (↙ (↙ (↙ (↘ here))))) → ⊴-refl
              (↙ (↙ (↙ (↘ _)))) → ⊴-refl
              (↙ (↙ (↘ _))) → ⊴-refl
              (↙ (↘ (there () _)))
              (↘ (there () _))
            )))
          (mk λ where
            (↙ (↙ (↙ (↙ (there () _)))))
            (↙ (↙ (↙ (↘ _)))) → ⊴-refl
            (↙ (↙ (↘ _))) → ⊴-refl
            (↙ (↘ _)) → ⊴-refl
            (↘ (there () _))
          )
          (`var (lvar
            (↙ (↙ (↘ here)))
            refl
            (mk λ where
              (↙ (↙ (↙ (↙ (↙ (there () _))))))
              (↙ (↙ (↙ (↙ (↘ _))))) → ⊴-refl
              (↙ (↙ (↙ (↘ _)))) → ⊴-refl
              (↙ (↙ (↘ here))) → ⊴-refl
              (↙ (↘ (there () _)))
              (↘ (there () _))
            )))))
        (mk λ where
          (↙ (↙ (↙ (there () _))))
          (↙ (↙ (↘ _))) → ⊴-refl
          (↙ (↘ _)) → ⊴-refl
          (↘ _) → ⊴-refl
        )
        (`var (lvar
          (↙ (↙ (↘ here)))
          refl
          (mk λ where
            (↙ (↙ (↙ (↙ (there () _)))))
            (↙ (↙ (↙ (↘ _)))) → ⊴-refl
            (↙ (↙ (↘ here))) → ⊴-refl
            (↙ (↘ _)) → ⊴-refl
            (↘ (there () _))
          )))))))

  myC′ : (A B C : Ty) → Term ((A ⊸ B ⊸ C) ⊸ (B ⊸ A ⊸ C)) []ᶜ
  myC′ A B C = lam (lam (lam
    (app B ((([] ++ [ u1 ]) ++ [ u0 ]) ++ [ u1 ])
           ((([] ++ [ u0 ]) ++ [ u1 ]) ++ [ u0 ])
           ((([]₂ ++₂ [ ⊴-refl ]₂) ++₂ [ ⊴-refl ]₂) ++₂ [ ⊴-refl ]₂)
      (app A (((([] ++ [ u1 ]) ++ [ u0 ]) ++ [ u0 ]) ++ [])
             (((([] ++ [ u0 ]) ++ [ u0 ]) ++ [ u1 ]) ++ [])
             (((([]₂ ++₂ [ ⊴-refl ]₂) ++₂ [ ⊴-refl ]₂) ++₂ [ ⊴-refl ]₂)
               ++₂ []₂)
        (var (↙ (↙ (↙ (↙ (↘ here)))))
             ((((([]₂ ++₂ [ ⊴-refl ]₂) ++₂ [ ⊴-refl ]₂) ++₂ [ ⊴-refl ]₂)
               ++₂ []₂) ++₂ []₂))
        (var (↙ (↙ (↘ here)))
             ((((([]₂ ++₂ [ ⊴-refl ]₂) ++₂ [ ⊴-refl ]₂) ++₂ [ ⊴-refl ]₂)
               ++₂ []₂) ++₂ []₂)))
      (var (↙ (↙ (↘ here)))
           (((([]₂ ++₂ [ ⊴-refl ]₂) ++₂ [ ⊴-refl ]₂) ++₂ [ ⊴-refl ]₂)
             ++₂ []₂)))))
  -}
