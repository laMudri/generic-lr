{-# OPTIONS --safe --sized-types --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ)
open import Relation.Binary using (Rel)

module Generic.Linear.Example.MuMuTilde
  (skewSemiring : SkewSemiring 0ℓ 0ℓ) (Base : Set)
  where

  open SkewSemiring skewSemiring
    renaming (Carrier to Ann
             ; _≤_ to _⊴_
             ; refl to ⊴-refl; trans to ⊴-trans
             )

  open import Algebra.Relational
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.Product as ×
  open import Data.Product.Relation.Binary.Pointwise.NonDependent as ×PW
    using (×-setoid)
  open import Data.Unit using (⊤; tt)
  open import Function.Base using (id; _∘_; _∘′_; _$_; λ-; _$-)
  open import Function.Equality using (_⟶_; _⇨_; _⟨$⟩_; cong)
  open import Size
  open import Relation.Unary
  open import Relation.Unary.Bunched
  open import Relation.Unary.Bunched.Properties
  open import Relation.Binary using (Setoid)
  open import Relation.Binary.Construct.Always as ⊤ using ()
  open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_; subst; subst₂)

  infixr 5 _⅋_
  infixl 6 _^⊥

  data Ty : Set where
    base : Ty
    _⅋_ : (rA sB : Ann × Ty) → Ty
    _^⊥ : (A : Ty) → Ty

  data Conc : Set where
    com : Conc
    trm cot : (A : Ty) → Conc

  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Algebra skewSemiring
  open import Generic.Linear.Syntax Conc Ann
  open import Generic.Linear.Syntax.Interpretation Conc rawSkewSemiring
  open import Generic.Linear.Syntax.Interpretation.Map Conc skewSemiring
  open import Generic.Linear.Syntax.Term Conc rawSkewSemiring
  open import Generic.Linear.Environment Conc rawSkewSemiring
    renaming (var to ivar)
  open import Generic.Linear.Thinning Conc rawSkewSemiring
  open _─Env
  open import Generic.Linear.Extend Conc skewSemiring
  open import Generic.Linear.Thinning.Properties Conc skewSemiring
  open import Generic.Linear.Environment.Properties Conc skewSemiring
  open import Generic.Linear.Semantics Conc skewSemiring

  data `MMT : Set where
    `cut `μ `μ∼ : (A : Ty) → `MMT
    `λ `λ∼ : (A : Ty) → `MMT
    `⟨-,-⟩ `μ⟨-,-⟩ : (rA sB : Ann × Ty) → `MMT

  MMT : System
  MMT = system `MMT λ where
    (`cut A) → rule (([]ᶜ `⊢ trm A) `* ([]ᶜ `⊢ cot A))
                    com
    (`μ A) → rule ([ 1# , cot A ]ᶜ `⊢ com)
                  (trm A)
    (`μ∼ A) → rule ([ 1# , trm A ]ᶜ `⊢ com)
                   (cot A)
    (`λ A) → rule ([]ᶜ `⊢ cot A)
                  (trm (A ^⊥))
    (`λ∼ A) → rule ([]ᶜ `⊢ trm A)
                   (cot (A ^⊥))
    (`⟨-,-⟩ rA@(r , A) sB@(s , B)) →
      rule ((r `· ([]ᶜ `⊢ cot A)) `* (s `· ([]ᶜ `⊢ cot B)))
           (cot (rA ⅋ sB))
    (`μ⟨-,-⟩ rA@(r , A) sB@(s , B)) →
      rule (([ r , cot A ]ᶜ ++ᶜ [ s , cot B ]ᶜ) `⊢ com)
           (trm (rA ⅋ sB))

  Drv = Tm MMT ∞
  open WithScope (Scope Drv)

  myComm : (rA sB : Ann × Ty) →
           Drv (trm ((1# , (rA ⅋ sB) ^⊥) ⅋ (1# , sB ⅋ rA))) []ᶜ
  myComm rA@(r , A) sB@(s , B) =
    `con (`μ⟨-,-⟩ _ _ , ≡.refl ,
      `con (`cut (sB ⅋ rA) , ≡.refl ,
        _✴⟨_⟩_
        {y = [] ++ ([ 1# ] ++ [ 0# ])}
        {z = [] ++ ([ 0# ] ++ [ 1# ])}
        (`con (`μ⟨-,-⟩ _ _ , ≡.refl ,
          `con (`cut ((rA ⅋ sB) ^⊥) , ≡.refl ,
            _✴⟨_⟩_
            {y = (([] ++ ([ 0# ] ++ [ 0# ])) ++ []) ++ ([ s ] ++ [ r ])}
            {z = (([] ++ ([ 1# ] ++ [ 0# ])) ++ []) ++ ([ 0# ] ++ [ 0# ])}
            (`con (`λ _ , ≡.refl ,
              `con (`⟨-,-⟩ _ _ , ≡.refl ,
                _✴⟨_⟩_
                {y = (((([] ++ ([ 0# ] ++ [ 0# ])) ++ []) ++ ([ 0# ] ++ [ r ])) ++ []) ++ []}
                {z = (((([] ++ ([ 0# ] ++ [ 0# ])) ++ []) ++ ([ s ] ++ [ 0# ])) ++ []) ++ []}
                (⟨_⟩·_
                  {z = (((([] ++ ([ 0# ] ++ [ 0# ])) ++ []) ++ ([ 0# ] ++ [ 1# ])) ++ []) ++ []}
                  ((((([]₂ ++₂ ([ annihil .proj₂ _ ]₂ ++₂ [ annihil .proj₂ _ ]₂)) ++₂ []₂) ++₂ ([ annihil .proj₂ _ ]₂ ++₂ [ *.identity .proj₂ _ ]₂)) ++₂ []₂) ++₂ []₂)
                  (`var (lvar (↙ (↙ (↙ (↘ (↘ here))))) ≡.refl
                              (((((([]₂ ++₂ ([ ⊴-refl ]₂ ++₂ [ ⊴-refl ]₂)) ++₂ []₂) ++₂ ([ ⊴-refl ]₂ ++₂ [ ⊴-refl ]₂)) ++₂ []₂) ++₂ []₂) ++₂ []₂))))
                ((((([]₂ ++₂ ([ +.identity-→ .proj₂ _ ]₂ ++₂ [ +.identity-→ .proj₂ _ ]₂)) ++₂ []₂) ++₂ ([ +.identity-← .proj₁ _ ]₂ ++₂ [ +.identity-→ .proj₂ _ ]₂)) ++₂ []₂) ++₂ []₂)
                (⟨_⟩·_
                  {z = (((([] ++ ([ 0# ] ++ [ 0# ])) ++ []) ++ ([ 1# ] ++ [ 0# ])) ++ []) ++ []}
                  ((((([]₂ ++₂ ([ annihil .proj₂ _ ]₂ ++₂ [ annihil .proj₂ _ ]₂)) ++₂ []₂) ++₂ ([ *.identity .proj₂ _ ]₂ ++₂ [ annihil .proj₂ _ ]₂)) ++₂ []₂) ++₂ []₂)
                  (`var (lvar (↙ (↙ (↙ (↘ (↙ here))))) ≡.refl
                              (((((([]₂ ++₂ ([ ⊴-refl ]₂ ++₂ [ ⊴-refl ]₂)) ++₂ []₂) ++₂ ([ ⊴-refl ]₂ ++₂ [ ⊴-refl ]₂)) ++₂ []₂) ++₂ []₂) ++₂ []₂)))))))
            ((([]₂ ++₂ ([ +.identity-← .proj₁ _ ]₂ ++₂ [ +.identity-← .proj₁ _ ]₂)) ++₂ []₂) ++₂ ([ +.identity-→ .proj₂ _ ]₂ ++₂ [ +.identity-→ .proj₂ _ ]₂))
            (`var (lvar (↙ (↙ (↙ (↘ (↙ here))))) ≡.refl
                        (((([]₂ ++₂ ([ ⊴-refl ]₂ ++₂ [ ⊴-refl ]₂)) ++₂ []₂) ++₂ ([ ⊴-refl ]₂ ++₂ [ ⊴-refl ]₂)) ++₂ []₂)))
          )
        ))
        ([]₂ ++₂ ([ +.identity-→ .proj₂ _ ]₂ ++₂ [ +.identity-← .proj₁ _ ]₂))
        (`var (lvar (↙ (↘ (↘ here))) ≡.refl
                    (([]₂ ++₂ ([ ⊴-refl ]₂ ++₂ [ ⊴-refl ]₂)) ++₂ []₂)))
      )
    )
