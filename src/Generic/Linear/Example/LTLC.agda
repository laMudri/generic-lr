{-# OPTIONS --sized-types --without-K --postfix-projections --prop #-}

module Generic.Linear.Example.LTLC where

  open import Algebra.Po
  open import Data.Bool
  open import Data.Empty
  open import Data.List as L using (List; _∷_) renaming ([] to []L)
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Automation
  open import Data.Product
  open import Data.Unit
  open import Function.Base
  open import Level
  open import Proposition
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
  open import Relation.Nullary.Decidable.Core  -- TODO: remove
  open import Relation.Unary.Bunched
  open import Size

  infixr 5 _⊸_

  open import Generic.Linear.Example.ZeroOneMany renaming (u01ω to Ann)

  data Ty : Set where
    ι : Ty
    _⊸_ : (A B : Ty) → Ty

  open import Generic.Linear.Syntax Ty Ann

  open import Generic.Linear.Syntax.Term Ty rawPoSemiring
  open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Renaming Ty poSemiring

  data `LTLC : Set where
    `lam `app : (A B : Ty) → `LTLC

  flags : PremisesFlags
  flags = record noPremisesFlags { Has-✴ = ⊤ᴾ }

  LTLC : System flags
  LTLC = `LTLC ▹ λ where
    (`lam A B) → ⟨ [(u1 , A)]ᶜ `⊢ B ⟩ =⇒ A ⊸ B
    (`app A B) → ⟨ []ᶜ `⊢ A ⊸ B ⟩ `✴ ⟨ []ᶜ `⊢ A ⟩ =⇒ B

  Term = [ LTLC , ∞ ]_⊢_

  pattern var i les = `var (lvar i refl les)
  pattern lam t = `con (`lam _ _ , refl , t)
  pattern app A P Q sp s t =
    `con (`app A _ , refl , _✴⟨_⟩_ {y = P} {z = Q} s sp t)

  open import Generic.Linear.Example.UsageCheck Ty
  open WithPoSemiring poSemiring
  open WithInverses flags record
    { 0#⁻¹ = u0⁻¹ ; +⁻¹ = +⁻¹ ; 1#⁻¹ = u1⁻¹ ; *⁻¹ = *⁻¹ ; rep = λ { {{()}} } }

  module V where

    open import Generic.Linear.Syntax.Term Ty U.0-rawPoSemiring public
    open import Generic.Linear.Syntax.Interpretation Ty U.0-rawPoSemiring
      public
    open import Generic.Linear.Variable Ty U.0-rawPoSemiring public
    open import Generic.Linear.Renaming Ty U.0-poSemiring public

  pattern uvar i = V.`var (V.lvar i refl _)
  pattern ulam t = V.`con (`lam _ _ , refl , t)
  pattern uapp s t =
    V.`con (`app _ _ , refl , s ✴⟨ _ ⟩ t)

  myC : (A B C : Ty) → Term []ᶜ ((A ⊸ B ⊸ C) ⊸ (B ⊸ A ⊸ C))
  myC A B C = elab-unique LTLC
    (ulam (ulam (ulam (uapp (uapp (uvar (# 0)) (uvar (# 2))) (uvar (# 1))))))
    []

  -- I have no idea why `# 1` isn't working in place of `#1`.
  myB : (A B C : Ty) → Term []ᶜ ((B ⊸ C) ⊸ (A ⊸ B) ⊸ (A ⊸ C))
  myB A B C = let #1 = ↙ (↙ (↙ (↘ here))) in elab-unique LTLC
    (ulam (ulam (ulam (uapp (uvar (# 0)) (uapp (uvar #1) (uvar (# 2)))))))
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
              (↙ (↙ (↙ (↙ (↘ here))))) → ≤-refl
              (↙ (↙ (↙ (↘ _)))) → ≤-refl
              (↙ (↙ (↘ _))) → ≤-refl
              (↙ (↘ (there () _)))
              (↘ (there () _))
            )))
          (mk λ where
            (↙ (↙ (↙ (↙ (there () _)))))
            (↙ (↙ (↙ (↘ _)))) → ≤-refl
            (↙ (↙ (↘ _))) → ≤-refl
            (↙ (↘ _)) → ≤-refl
            (↘ (there () _))
          )
          (`var (lvar
            (↙ (↙ (↘ here)))
            refl
            (mk λ where
              (↙ (↙ (↙ (↙ (↙ (there () _))))))
              (↙ (↙ (↙ (↙ (↘ _))))) → ≤-refl
              (↙ (↙ (↙ (↘ _)))) → ≤-refl
              (↙ (↙ (↘ here))) → ≤-refl
              (↙ (↘ (there () _)))
              (↘ (there () _))
            )))))
        (mk λ where
          (↙ (↙ (↙ (there () _))))
          (↙ (↙ (↘ _))) → ≤-refl
          (↙ (↘ _)) → ≤-refl
          (↘ _) → ≤-refl
        )
        (`var (lvar
          (↙ (↙ (↘ here)))
          refl
          (mk λ where
            (↙ (↙ (↙ (↙ (there () _)))))
            (↙ (↙ (↙ (↘ _)))) → ≤-refl
            (↙ (↙ (↘ here))) → ≤-refl
            (↙ (↘ _)) → ≤-refl
            (↘ (there () _))
          )))))))

  myC′ : (A B C : Ty) → Term []ᶜ ((A ⊸ B ⊸ C) ⊸ (B ⊸ A ⊸ C))
  myC′ A B C = lam (lam (lam
    (app B ((([] ++ [ u1 ]) ++ [ u0 ]) ++ [ u1 ])
           ((([] ++ [ u0 ]) ++ [ u1 ]) ++ [ u0 ])
           ((([]₂ ++₂ [ ≤-refl ]₂) ++₂ [ ≤-refl ]₂) ++₂ [ ≤-refl ]₂)
      (app A (((([] ++ [ u1 ]) ++ [ u0 ]) ++ [ u0 ]) ++ [])
             (((([] ++ [ u0 ]) ++ [ u0 ]) ++ [ u1 ]) ++ [])
             (((([]₂ ++₂ [ ≤-refl ]₂) ++₂ [ ≤-refl ]₂) ++₂ [ ≤-refl ]₂)
               ++₂ []₂)
        (var (↙ (↙ (↙ (↙ (↘ here)))))
             ((((([]₂ ++₂ [ ≤-refl ]₂) ++₂ [ ≤-refl ]₂) ++₂ [ ≤-refl ]₂)
               ++₂ []₂) ++₂ []₂))
        (var (↙ (↙ (↘ here)))
             ((((([]₂ ++₂ [ ≤-refl ]₂) ++₂ [ ≤-refl ]₂) ++₂ [ ≤-refl ]₂)
               ++₂ []₂) ++₂ []₂)))
      (var (↙ (↙ (↘ here)))
           (((([]₂ ++₂ [ ≤-refl ]₂) ++₂ [ ≤-refl ]₂) ++₂ [ ≤-refl ]₂)
             ++₂ []₂)))))
  -}
