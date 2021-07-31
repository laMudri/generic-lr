{-# OPTIONS --sized-types --without-K --postfix-projections --prop #-}

open import Algebra.Po
open import Level using (0ℓ)
open import Relation.Binary using (Rel)

module Generic.Linear.Example.MuMuTilde
  (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ) (Base : Set)
  where

  open PoSemiring poSemiring renaming (Carrier to Ann)

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
  open import Proposition
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

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Conc Ann
  open import Generic.Linear.Syntax.Interpretation Conc rawPoSemiring
  open import Generic.Linear.Syntax.Interpretation.Map Conc poSemiring
  open import Generic.Linear.Syntax.Term Conc rawPoSemiring
  open import Generic.Linear.Variable Conc rawPoSemiring
  open import Generic.Linear.Environment Conc poSemiring
  open import Generic.Linear.Renaming Conc poSemiring
  open [_]_⇒ᵉ_
  open import Generic.Linear.Extend Conc poSemiring
  open import Generic.Linear.Renaming.Properties Conc poSemiring
  open import Generic.Linear.Environment.Properties Conc poSemiring
  open import Generic.Linear.Semantics Conc poSemiring

  data `MMT : Set where
    `cut `μ `μ∼ : (A : Ty) → `MMT
    `λ `λ∼ : (A : Ty) → `MMT
    `⟨-,-⟩ `μ⟨-,-⟩ : (rA sB : Ann × Ty) → `MMT

  flags : PremisesFlags
  flags = allPremisesFlags

  MMT : System flags
  MMT = `MMT ▹ λ where
    (`cut A) → ⟨ []ᶜ `⊢ trm A ⟩ `✴ ⟨ []ᶜ `⊢ cot A ⟩
               =⇒ com
    (`μ A) → ⟨ [ 1# , cot A ]ᶜ `⊢ com ⟩
             =⇒ trm A
    (`μ∼ A) → ⟨ [ 1# , trm A ]ᶜ `⊢ com ⟩
              =⇒ cot A
    (`λ A) → ⟨ []ᶜ `⊢ cot A ⟩
             =⇒ trm (A ^⊥)
    (`λ∼ A) → ⟨ []ᶜ `⊢ trm A ⟩
              =⇒ cot (A ^⊥)
    (`⟨-,-⟩ rA@(r , A) sB@(s , B)) →
      r `· ⟨ []ᶜ `⊢ cot A ⟩ `✴ s `· ⟨ []ᶜ `⊢ cot B ⟩
      =⇒ cot (rA ⅋ sB)
    (`μ⟨-,-⟩ rA@(r , A) sB@(s , B)) →
      ⟨ [ r , cot A ]ᶜ ++ᶜ [ s , cot B ]ᶜ `⊢ com ⟩
      =⇒ trm (rA ⅋ sB)

  Drv = [ MMT , ∞ ]_⊢_
  open WithScope (Scope Drv)

  myComm : (rA sB : Ann × Ty) →
           Drv []ᶜ (trm ((1# , (rA ⅋ sB) ^⊥) ⅋ (1# , sB ⅋ rA)))
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
                  ((((([]ₙ ++ₙ ([ ≤-annihil .proj₂ _ ]ₙ ++ₙ [ ≤-annihil .proj₂ _ ]ₙ)) ++ₙ []ₙ) ++ₙ ([ ≤-annihil .proj₂ _ ]ₙ ++ₙ [ *.identity .proj₂ _ ]ₙ)) ++ₙ []ₙ) ++ₙ []ₙ)
                  (`var (lvar (↙ (↙ (↙ (↘ (↘ here))))) ≡.refl
                              (((((([]ₙ ++ₙ ([ ≤-refl ]ₙ ++ₙ [ ≤-refl ]ₙ)) ++ₙ []ₙ) ++ₙ ([ ≤-refl ]ₙ ++ₙ [ ≤-refl ]ₙ)) ++ₙ []ₙ) ++ₙ []ₙ) ++ₙ []ₙ))))
                ((((([]ₙ ++ₙ ([ +.identity-→ .proj₂ _ ]ₙ ++ₙ [ +.identity-→ .proj₂ _ ]ₙ)) ++ₙ []ₙ) ++ₙ ([ +.identity-← .proj₁ _ ]ₙ ++ₙ [ +.identity-→ .proj₂ _ ]ₙ)) ++ₙ []ₙ) ++ₙ []ₙ)
                (⟨_⟩·_
                  {z = (((([] ++ ([ 0# ] ++ [ 0# ])) ++ []) ++ ([ 1# ] ++ [ 0# ])) ++ []) ++ []}
                  ((((([]ₙ ++ₙ ([ ≤-annihil .proj₂ _ ]ₙ ++ₙ [ ≤-annihil .proj₂ _ ]ₙ)) ++ₙ []ₙ) ++ₙ ([ *.identity .proj₂ _ ]ₙ ++ₙ [ ≤-annihil .proj₂ _ ]ₙ)) ++ₙ []ₙ) ++ₙ []ₙ)
                  (`var (lvar (↙ (↙ (↙ (↘ (↙ here))))) ≡.refl
                              (((((([]ₙ ++ₙ ([ ≤-refl ]ₙ ++ₙ [ ≤-refl ]ₙ)) ++ₙ []ₙ) ++ₙ ([ ≤-refl ]ₙ ++ₙ [ ≤-refl ]ₙ)) ++ₙ []ₙ) ++ₙ []ₙ) ++ₙ []ₙ)))))))
            ((([]ₙ ++ₙ ([ +.identity-← .proj₁ _ ]ₙ ++ₙ [ +.identity-← .proj₁ _ ]ₙ)) ++ₙ []ₙ) ++ₙ ([ +.identity-→ .proj₂ _ ]ₙ ++ₙ [ +.identity-→ .proj₂ _ ]ₙ))
            (`var (lvar (↙ (↙ (↙ (↘ (↙ here))))) ≡.refl
                        (((([]ₙ ++ₙ ([ ≤-refl ]ₙ ++ₙ [ ≤-refl ]ₙ)) ++ₙ []ₙ) ++ₙ ([ ≤-refl ]ₙ ++ₙ [ ≤-refl ]ₙ)) ++ₙ []ₙ)))
          )
        ))
        ([]ₙ ++ₙ ([ +.identity-→ .proj₂ _ ]ₙ ++ₙ [ +.identity-← .proj₁ _ ]ₙ))
        (`var (lvar (↙ (↘ (↘ here))) ≡.refl
                    (([]ₙ ++ₙ ([ ≤-refl ]ₙ ++ₙ [ ≤-refl ]ₙ)) ++ₙ []ₙ)))
      )
    )
