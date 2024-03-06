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
  open import Generic.Linear.Example.ZeroOneMany renaming (0#1ω to Ann)

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

    LR : System
    LR = `LR ▹ λ where
      (`0e Z) → (⟨ []ᶜ `⊢ t0 ⟩ `✴ `⊤) `⊆ Z
      (`⊕i i A B) → ⟨ []ᶜ `⊢ [ A > i < B ] ⟩ `⊆ A t⊕ B
      (`⊕e A B Z) →
        ⟨ []ᶜ `⊢ A t⊕ B ⟩ `✴ (⟨ [ 1# , A ]ᶜ `⊢ Z ⟩ `∧ ⟨ [ 1# , B ]ᶜ `⊢ Z ⟩)
        `⊆ Z
      `⊤i → `⊤ `⊆ t⊤
      (`&i A B) → ⟨ []ᶜ `⊢ A ⟩ `∧ ⟨ []ᶜ `⊢ B ⟩ `⊆ A t& B
      (`&e i A B) → ⟨ []ᶜ `⊢ A t& B ⟩ `⊆ [ A > i < B ]
      `Ii → `ℑ `⊆ tI
      (`Ie Z) → ⟨ []ᶜ `⊢ tI ⟩ `✴ ⟨ []ᶜ `⊢ Z ⟩ `⊆ Z
      (`⊗i A B) → ⟨ []ᶜ `⊢ A ⟩ `✴ ⟨ []ᶜ `⊢ B ⟩ `⊆ A t⊗ B
      (`⊗e A B Z) →
        (⟨ []ᶜ `⊢ A t⊗ B ⟩ `✴ ⟨ [ 1# , A ]ᶜ ++ᶜ [ 1# , B ]ᶜ `⊢ Z ⟩) `⊆ Z
      (`⊸i A B) → ⟨ [ 1# , A ]ᶜ `⊢ B ⟩ `⊆ A t⊸ B
      (`⊸e A B) → ⟨ []ᶜ `⊢ A t⊸ B ⟩ `✴ ⟨ []ᶜ `⊢ A ⟩ `⊆ B
      (`!i A) → ω# `· ⟨ []ᶜ `⊢ A ⟩ `⊆ t! A
      (`!e A Z) → ⟨ []ᶜ `⊢ t! A ⟩ `✴ ⟨ [ ω# , A ]ᶜ `⊢ Z ⟩ `⊆ Z
      `ze → `ℑ `⊆ nat
      `su → ⟨ []ᶜ `⊢ nat ⟩ `⊆ nat
      (`iter Z) →
        ⟨ []ᶜ `⊢ nat ⟩ `✴ `□⁰⁺ˣ (⟨ []ᶜ `⊢ Z ⟩ `∧ ⟨ [ 1# , Z ]ᶜ `⊢ Z ⟩) `⊆ Z

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
    open WithInverses record
      { 0#⁻¹ = 0#⁻¹ ; +⁻¹ = +⁻¹ ; 1#⁻¹ = 1#⁻¹ ; *⁻¹ = *⁻¹ ; rep = rep }
      public

    module V where

      open import Generic.Linear.Syntax.Term Ty U.0-rawPoSemiring public
      open import Generic.Linear.Syntax.Interpretation Ty U.0-rawPoSemiring
        public
      open import Generic.Linear.Variable Ty U.0-rawPoSemiring public
      open import Generic.Linear.Renaming Ty U.0-poSemiring public

    pattern u⊸i t = V.`con (`⊸i _ _ , refl , t)
    pattern u⊸e f s = V.`con (`⊸e _ _ , refl , f ✴ᶜ⟨ _ ⟩ s)
    pattern u!i s = V.`con (`!i _ , refl , ⟨ _ ⟩·ᶜ s)
    pattern u!e T e t = V.`con (`!e _ T , refl , e ✴ᶜ⟨ _ ⟩ t)
    pattern uze = V.`con (`ze , refl , ℑᶜ⟨ _ ⟩)
    pattern usu s = V.`con (`su , refl , s)
    pattern uiter T e s t =
      V.`con (`iter T , refl , e ✴ᶜ⟨ _ ⟩ (□ᶜ⟨ _ ⟩ (s , t)))

  private
    open WithLLFlags allLLFlags

    myK : ∀ A B → Term []ᶜ (t! (A t⊸ B) t⊸ t! A t⊸ t! B)
    myK A B =
      let #1 : Ptr ((((ε <+> [-]) <+> [-]) <+> [-]) <+> ε)
          #1 = # 1 in
      elab-unique LR
        (u⊸i (u⊸i (u!e _ (uvar# 0) (u!e _ (uvar #1)
          (u!i (u⊸e (uvar# 2) (uvar# 3)))))))
        []

    deepid : Term []ᶜ (nat t⊸ nat)
    deepid = elab-unique LR
      (u⊸i (uiter _ (uvar# 0) uze (usu (uvar# 1))))
      []

    -- dupNat : nat t⊸ t! ω# nat
    -- dupNat = λn. iter n return t! ω# nat where
    --   0          ↦ !i 0
    --   suc _ | ih ↦ let !i m = ih return t! ω# nat in
    --                !i (suc m)

    dupNat : Term []ᶜ (nat t⊸ t! nat)
    dupNat =
      let #1 : Ptr (((ε <+> [-]) <+> [-]) <+> ε)
          #1 = # 1 in
      elab-unique LR
        (u⊸i (uiter (t! nat) (uvar# 0)
          (u!i uze)
          (u!e (t! nat) (uvar #1)
            (u!i (usu (uvar# 2))))))
        []
