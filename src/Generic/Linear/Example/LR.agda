{-# OPTIONS --sized-types --without-K --prop --postfix-projections #-}

module Generic.Linear.Example.LR where

  open import Algebra.Po
  open import Data.Bool.Base
  open import Data.Hand
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Automation
  open import Data.Product
  open import Data.Sum
  open import Data.Unit
  open import Function.Equality
  open import Function.Equivalence
  open import Level
  open import Proposition
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Relation.Unary.Bunched
  open import Size

  open import Generic.Linear.Example.LLFlags
  open import Generic.Linear.Example.ZeroOneMany renaming (u01ω to Ann)

  module WithLLFlags (llfl : LLFlags) where

    open LLFlags llfl

    infixr 5 _t⊕_ _t&_ _t⊗_ _t⊸_

    data Ty : Set where
      ι : Ty
      t0 : {{_ : Has-0}} → Ty
      _t⊕_ : {{_ : Has-⊕}} (A B : Ty) → Ty
      t⊤ : {{_ : Has-⊤}} → Ty
      _t&_ : {{_ : Has-&}} (A B : Ty) → Ty
      tI : {{_ : Has-I}} → Ty
      _t⊗_ : {{_ : Has-⊗}} (A B : Ty) → Ty
      _t⊸_ : {{_ : Has-⊸}} (A B : Ty) → Ty
      -- TODO: we could generally consider restrictions on the ! annotation,
      -- rather than committing to ω.
      t! : {{_ : Has-!}} (A : Ty) → Ty
      nat : {{_ : Has-ℕ}} → Ty

    open import Generic.Linear.Syntax Ty Ann public

    open import Generic.Linear.Syntax.Term Ty rawPoSemiring public
    open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring public
    open import Generic.Linear.Variable Ty rawPoSemiring public
    open import Generic.Linear.Renaming Ty poSemiring public

    data `LR : Set where
      `0e : {{_ : Has-0}} (Z : Ty) → `LR
      `⊕i : {{_ : Has-⊕}} (i : Hand) (A B : Ty) → `LR
      `⊕e : {{_ : Has-⊕}} (A B Z : Ty) → `LR
      `⊤i : {{_ : Has-⊤}} → `LR
      `&i : {{_ : Has-&}} (A B : Ty) → `LR
      `&e : {{_ : Has-&}} (i : Hand) (A B : Ty) → `LR
      `Ii : {{_ : Has-I}} → `LR
      `Ie : {{_ : Has-I}} (Z : Ty) → `LR
      `⊗i : {{_ : Has-⊗}} (A B : Ty) → `LR
      `⊗e : {{_ : Has-⊗}} (A B Z : Ty) → `LR
      `⊸i `⊸e : {{_ : Has-⊸}} (A B : Ty) → `LR
      `!i : {{_ : Has-!}} (A : Ty) → `LR
      `!e : {{_ : Has-!}} (A Z : Ty) → `LR
      `ze `su : {{_ : Has-ℕ}} → `LR
      `iter : {{_ : Has-ℕ}} (Z : Ty) → `LR

    flags : PremisesFlags
    flags = allPremisesFlags
      -- NOTE: the following are the precise flags required, but instance
      -- search (with --overlapping-instances) takes too long.
      -- record noPremisesFlags
      -- { Has-⊤ = Has-0 ∨ᴾ Has-⊤
      -- ; Has-∧ = Has-⊕ ∨ᴾ Has-& ∨ᴾ Has-ℕ
      -- ; Has-ℑ = Has-I ∨ᴾ Has-ℕ
      -- ; Has-✴ = Has-0 ∨ᴾ Has-⊕ ∨ᴾ Has-I ∨ᴾ Has-⊗ ∨ᴾ Has-⊸ ∨ᴾ Has-! ∨ᴾ Has-ℕ
      -- ; Has-· = Has-!
      -- ; Has-□ = Has-ℕ
      -- }

    LR : System flags
    LR = `LR ▹ λ where
      (`0e Z) → (⟨ []ᶜ `⊢ t0 ⟩ `✴ `⊤) =⇒ Z
      (`⊕i i A B) → ⟨ []ᶜ `⊢ [ A > i < B ] ⟩ =⇒ A t⊕ B
      (`⊕e A B Z) →
        ⟨ []ᶜ `⊢ A t⊕ B ⟩ `✴ (⟨ [ u1 , A ]ᶜ `⊢ Z ⟩ `∧ ⟨ [ u1 , B ]ᶜ `⊢ Z ⟩)
        =⇒ Z
      `⊤i → `⊤ =⇒ t⊤
      (`&i A B) → ⟨ []ᶜ `⊢ A ⟩ `∧ ⟨ []ᶜ `⊢ B ⟩ =⇒ A t& B
      (`&e i A B) → ⟨ []ᶜ `⊢ A t& B ⟩ =⇒ [ A > i < B ]
      `Ii → `ℑ =⇒ tI
      (`Ie Z) → ⟨ []ᶜ `⊢ tI ⟩ `✴ ⟨ []ᶜ `⊢ Z ⟩ =⇒ Z
      (`⊗i A B) → ⟨ []ᶜ `⊢ A ⟩ `✴ ⟨ []ᶜ `⊢ B ⟩ =⇒ A t⊗ B
      (`⊗e A B Z) →
        (⟨ []ᶜ `⊢ A t⊗ B ⟩ `✴ ⟨ [ u1 , A ]ᶜ ++ᶜ [ u1 , B ]ᶜ `⊢ Z ⟩) =⇒ Z
      (`⊸i A B) → ⟨ [ u1 , A ]ᶜ `⊢ B ⟩ =⇒ A t⊸ B
      (`⊸e A B) → ⟨ []ᶜ `⊢ A t⊸ B ⟩ `✴ ⟨ []ᶜ `⊢ A ⟩ =⇒ B
      (`!i A) → uω `· ⟨ []ᶜ `⊢ A ⟩ =⇒ t! A
      (`!e A Z) → ⟨ []ᶜ `⊢ t! A ⟩ `✴ ⟨ [ uω , A ]ᶜ `⊢ Z ⟩ =⇒ Z
      `ze → `ℑ =⇒ nat
      `su → ⟨ []ᶜ `⊢ nat ⟩ =⇒ nat
      (`iter Z) →
        let bf = boxFlags true true false in
        ⟨ []ᶜ `⊢ nat ⟩ `✴ `□ bf (⟨ []ᶜ `⊢ Z ⟩ `∧ ⟨ [ u1 , Z ]ᶜ `⊢ Z ⟩) =⇒ Z

    Term = [ LR , ∞ ]_⊢_

    pattern var i les = `var (lvar i refl les)
    pattern ⊸i t = `con (`⊸i _ _ , refl , t)
    pattern ⊸e P Q sp f s =
      `con (`⊸e _ _ , refl , _✴⟨_⟩_ {y = P} {z = Q} f sp s)
    pattern !i P sp s = `con (`!i _ _ , refl , ⟨_⟩·_ {z = P} sp s)
    pattern !e T P Q sp e t =
      `con (`!e _ _ T , refl , _✴⟨_⟩_ {y = P} {z = Q} e sp t)

    open import Generic.Linear.Example.UsageCheck Ty public
    open WithPoSemiring poSemiring public
    open WithInverses flags record
      { 0#⁻¹ = u0⁻¹ ; +⁻¹ = +⁻¹ ; 1#⁻¹ = u1⁻¹ ; *⁻¹ = *⁻¹ ; rep = rep }
      public

    module V where

      open import Generic.Linear.Syntax.Term Ty U.0-rawPoSemiring public
      open import Generic.Linear.Syntax.Interpretation Ty U.0-rawPoSemiring
        public
      open import Generic.Linear.Variable Ty U.0-rawPoSemiring public
      open import Generic.Linear.Renaming Ty U.0-poSemiring public

    pattern uvar i = V.`var (V.lvar i refl _)
    pattern u⊸i t = V.`con (`⊸i _ _ , refl , t)
    pattern u⊸e f s = V.`con (`⊸e _ _ , refl , f ✴⟨ _ ⟩ s)
    pattern u!i s = V.`con (`!i _ , refl , ⟨ _ ⟩· s)
    pattern u!e T e t = V.`con (`!e _ T , refl , e ✴⟨ _ ⟩ t)
    pattern uze = V.`con (`ze , refl , ℑ⟨ _ ⟩)
    pattern usu s = V.`con (`su , refl , s)
    pattern uiter T e s t =
      V.`con (`iter T , refl , e ✴⟨ _ ⟩ (□⟨ _ , _ , _ , _ ⟩ (s , t)))

  private
    open WithLLFlags allLLFlags

    myK : ∀ A B → Term []ᶜ (t! (A t⊸ B) t⊸ t! A t⊸ t! B)
    myK A B = elab-unique LR
      (u⊸i (u⊸i (u!e _ (uvar (# 0)) (u!e _ (uvar (# 1))
        (u!i (u⊸e (uvar (# 2)) (uvar (# 3))))))))
      []

    deepid : Term []ᶜ (nat t⊸ nat)
    deepid = elab-unique LR
      (u⊸i (uiter _ (uvar (# 0)) uze (usu (uvar (# 1)))))
      []

    -- dupNat : nat t⊸ t! uω nat
    -- dupNat = λn. iter n return t! uω nat where
    --   0          ↦ !i 0
    --   suc _ | ih ↦ let !i m = ih return t! uω nat in
    --                !i (suc m)

    dupNat : Term []ᶜ (nat t⊸ t! nat)
    dupNat = elab-unique LR
      (u⊸i (uiter (t! nat) (uvar (# 0))
        (u!i uze)
        (u!e (t! nat) (uvar (# 1))
          (u!i (usu (uvar (# 2)))))))
      []
