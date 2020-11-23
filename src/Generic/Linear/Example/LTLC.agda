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

  infix 7 _*_
  infix 6 _+_
  infixr 5 _⊸_
  infix 4 _⊴_

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
  u1 * b = b
  uω * u0 = u0
  uω * u1 = uω
  uω * uω = uω

  rawSkewSemiring : RawSkewSemiring 0ℓ 0ℓ
  rawSkewSemiring = record
    { rawProset = record { Carrier = Ann; _≤_ = _⊴_ }
    ; 0# = u0
    ; _+_ = _+_
    ; 1# = u1
    ; _*_ = _*_
    }

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

  -- With laws

  ⊴-trans : ∀ {x y z} → x ⊴ y → y ⊴ z → x ⊴ z
  ⊴-trans ⊴-refl yz = yz
  ⊴-trans ω⊴0 ⊴-refl = ω⊴0
  ⊴-trans ω⊴1 ⊴-refl = ω⊴1

  uω⊴ : ∀ {x} → uω ⊴ x
  uω⊴ {u0} = ω⊴0
  uω⊴ {u1} = ω⊴1
  uω⊴ {uω} = ⊴-refl

  +-mono : ∀ {x x′ y y′} → x ⊴ x′ → y ⊴ y′ → x + y ⊴ x′ + y′
  +-mono ⊴-refl ⊴-refl = ⊴-refl
  +-mono {x = u0} ⊴-refl ω⊴0 = ω⊴0
  +-mono {x = u1} ⊴-refl ω⊴0 = ω⊴1
  +-mono {x = uω} ⊴-refl ω⊴0 = ⊴-refl
  +-mono {x = u0} ⊴-refl ω⊴1 = ω⊴1
  +-mono {x = u1} ⊴-refl ω⊴1 = ⊴-refl
  +-mono {x = uω} ⊴-refl ω⊴1 = ⊴-refl
  +-mono ω⊴0 ⊴-refl = uω⊴
  +-mono ω⊴0 ω⊴0 = ω⊴0
  +-mono ω⊴0 ω⊴1 = ω⊴1
  +-mono ω⊴1 ⊴-refl = uω⊴
  +-mono ω⊴1 ω⊴0 = ω⊴1
  +-mono ω⊴1 ω⊴1 = ⊴-refl

  *-mono : ∀ {x x′ y y′} → x ⊴ x′ → y ⊴ y′ → x * y ⊴ x′ * y′
  *-mono ⊴-refl ⊴-refl = ⊴-refl
  *-mono {x = u0} ⊴-refl ω⊴0 = ⊴-refl
  *-mono {x = u1} ⊴-refl ω⊴0 = ω⊴0
  *-mono {x = uω} ⊴-refl ω⊴0 = ω⊴0
  *-mono {x = u0} ⊴-refl ω⊴1 = ⊴-refl
  *-mono {x = u1} ⊴-refl ω⊴1 = ω⊴1
  *-mono {x = uω} ⊴-refl ω⊴1 = ⊴-refl
  *-mono {y = u0} ω⊴0 yy = ⊴-refl
  *-mono {y = u1} ω⊴0 yy = ω⊴0
  *-mono {y = uω} ω⊴0 yy = ω⊴0
  *-mono {y = u0} ω⊴1 yy = yy
  *-mono {y = u1} ω⊴1 yy = uω⊴
  *-mono {y = uω} ω⊴1 yy = uω⊴

  ≡⇒⊴ : ∀ {x y} → x ≡ y → x ⊴ y
  ≡⇒⊴ refl = ⊴-refl

  +-identityʳ : ∀ x → x + u0 ≡ x
  +-identityʳ u0 = refl
  +-identityʳ u1 = refl
  +-identityʳ uω = refl

  +-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
  +-assoc u0 y z = refl
  +-assoc u1 u0 z = refl
  +-assoc u1 u1 u0 = refl
  +-assoc u1 u1 u1 = refl
  +-assoc u1 u1 uω = refl
  +-assoc u1 uω z = refl
  +-assoc uω y z = refl

  +-comm : ∀ x y → x + y ⊴ y + x
  +-comm u0 u0 = ⊴-refl
  +-comm u0 u1 = ⊴-refl
  +-comm u0 uω = ⊴-refl
  +-comm u1 u0 = ⊴-refl
  +-comm u1 u1 = ⊴-refl
  +-comm u1 uω = ⊴-refl
  +-comm uω u0 = ⊴-refl
  +-comm uω u1 = ⊴-refl
  +-comm uω uω = ⊴-refl

  ⊴*u1 : ∀ x → x ⊴ x * u1
  ⊴*u1 u0 = ⊴-refl
  ⊴*u1 u1 = ⊴-refl
  ⊴*u1 uω = ⊴-refl

  *-assoc : ∀ x y z → (x * y) * z ⊴ x * (y * z)
  *-assoc u0 y z = ⊴-refl
  *-assoc u1 y z = ⊴-refl
  *-assoc uω u0 z = ⊴-refl
  *-assoc uω u1 z = ⊴-refl
  *-assoc uω uω u0 = ⊴-refl
  *-assoc uω uω u1 = ⊴-refl
  *-assoc uω uω uω = ⊴-refl

  annihilʳ : ∀ x → u0 ⊴ x * u0
  annihilʳ u0 = ⊴-refl
  annihilʳ u1 = ⊴-refl
  annihilʳ uω = ⊴-refl

  distribˡ : ∀ x y z → (x + y) * z ⊴ x * z + y * z
  distribˡ u0 y z = ⊴-refl
  distribˡ u1 u0 u0 = ⊴-refl
  distribˡ u1 u0 u1 = ⊴-refl
  distribˡ u1 u0 uω = ⊴-refl
  distribˡ u1 u1 u0 = ⊴-refl
  distribˡ u1 u1 u1 = ⊴-refl
  distribˡ u1 u1 uω = ⊴-refl
  distribˡ u1 uω u0 = ⊴-refl
  distribˡ u1 uω u1 = ⊴-refl
  distribˡ u1 uω uω = ⊴-refl
  distribˡ uω u0 u0 = ⊴-refl
  distribˡ uω u1 u0 = ⊴-refl
  distribˡ uω uω u0 = ⊴-refl
  distribˡ uω y u1 = ⊴-refl
  distribˡ uω y uω = ⊴-refl

  distribʳ : ∀ x y z → x * y + x * z ⊴ x * (y + z)
  distribʳ u0 y z = ⊴-refl
  distribʳ u1 y z = ⊴-refl
  distribʳ uω u0 z = ⊴-refl
  distribʳ uω u1 u0 = ⊴-refl
  distribʳ uω u1 u1 = ⊴-refl
  distribʳ uω u1 uω = ⊴-refl
  distribʳ uω uω z = ⊴-refl

  skewSemiring : SkewSemiring 0ℓ 0ℓ
  skewSemiring = record
    { proset = record
      { _≤_ = _⊴_
      ; isProset = record { refl = ⊴-refl ; trans = ⊴-trans }
      }
    ; 0# = u0
    ; plus = record { _∙_ = _+_ ; mono = +-mono }
    ; 1# = u1
    ; mult = record { _∙_ = _*_ ; mono = *-mono }
    ; isSkewSemiring = record
      { +-isSkewCommutativeMonoid = record
        { isLeftSkewMonoid = record
          { identity = λ- ⊴-refl , ≡⇒⊴ ∘ sym ∘ +-identityʳ
          ; assoc = λ x y z → ≡⇒⊴ (+-assoc x y z)
          }
        ; isRightSkewMonoid = record
          { identity = λ- ⊴-refl , ≡⇒⊴ ∘ +-identityʳ
          ; assoc = λ x y z → ≡⇒⊴ (sym (+-assoc x y z))
          }
        ; comm = +-comm
        }
      ; *-isSkewMonoid = record
        { identity = λ- ⊴-refl , ⊴*u1
        ; assoc = *-assoc
        }
      ; annihil = λ- ⊴-refl , annihilʳ
      ; distrib = distribˡ , distribʳ
      }
    }

  u0⁻¹ : ∀ x → List (x ⊴ u0)
  u0⁻¹ u0 = ⊴-refl ∷ []L
  u0⁻¹ u1 = []L
  u0⁻¹ uω = ω⊴0 ∷ []L

  +⁻¹ : ∀ x → List (∃ \ ((y , z) : _ × _) → x ⊴ y + z)
  +⁻¹ u0 = ((u0 , u0) , ⊴-refl) ∷ []L
  +⁻¹ u1 = ((u1 , u0) , ⊴-refl) ∷ ((u0 , u1) , ⊴-refl) ∷ []L
  +⁻¹ uω = ((uω , uω) , ⊴-refl) ∷ []L

  u1⁻¹ : ∀ x → List (x ⊴ u1)
  u1⁻¹ u0 = []L
  u1⁻¹ u1 = ⊴-refl ∷ []L
  u1⁻¹ uω = ω⊴1 ∷ []L

  *⁻¹ : ∀ x z → List (∃ \ y → z ⊴ x * y)
  *⁻¹ u0 u0 = (uω , ⊴-refl) ∷ []L
  *⁻¹ u0 u1 = []L
  *⁻¹ u0 uω = []L
  *⁻¹ u1 z = (z , ⊴-refl) ∷ []L
  *⁻¹ uω u0 = (u0 , ⊴-refl) ∷ []L
  *⁻¹ uω u1 = []L
  *⁻¹ uω uω = (uω , ⊴-refl) ∷ []L

  open import Generic.Linear.Example.UsageCheck Ty skewSemiring
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

  Lone : ∀ {a} {A : Set a} → List A → Set
  Lone []L = ⊥
  Lone (x ∷ []L) = ⊤
  Lone (x ∷ y ∷ _) = ⊥

  getLone : ∀ {a} {A : Set a} (xs : List A) {_ : Lone xs} → A
  getLone (x ∷ []L) = x

  myC : (A B C : Ty) → Term ((A ⊸ B ⊸ C) ⊸ (B ⊸ A ⊸ C)) []ᶜ
  myC A B C = getLone foo
    where
    foo : List (Term ((A ⊸ B ⊸ C) ⊸ (B ⊸ A ⊸ C)) []ᶜ)
    foo = elab LTLC
      (ulam (ulam (ulam
        (uapp (uapp (uvar (↙ (↙ (↙ (↙ (↘ here))))))
                    (uvar (↙ (↙ (↘ here)))))
              (uvar (↙ (↙ (↘ here))))))))
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
