
{-# OPTIONS --sized-types --without-K --postfix-projections #-}

open import Algebra.Po
open import Level using (Level; 0ℓ; suc)
open import Relation.Binary using (Rel)

module Generic.Linear.Example.UsageCheck (Ty : Set) where

  open import Data.Empty
  open import Data.List as L using (List; []; _∷_)
  open import Data.Unit hiding (_≤_)

  Lone : ∀ {a} {A : Set a} → List A → Set
  Lone [] = ⊥
  Lone (x ∷ []) = ⊤
  Lone (x ∷ y ∷ _) = ⊥

  getLone : ∀ {a} {A : Set a} (xs : List A) {_ : Lone xs} → A
  getLone (x ∷ []) = x

  module U where




    0-poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ
    0-poSemiring = record
      { Carrier = ⊤; _≈_ = λ _ _ → ⊤; _≤_ = λ _ _ → ⊤ }




    0-rawPoSemiring : RawPoSemiring 0ℓ 0ℓ 0ℓ
    0-rawPoSemiring = PoSemiring.rawPoSemiring 0-poSemiring

    open import Generic.Linear.Operations 0-rawPoSemiring public
    open import Generic.Linear.Algebra 0-poSemiring public
    open import Generic.Linear.Syntax Ty ⊤ public
    open import Generic.Linear.Syntax.Interpretation Ty 0-rawPoSemiring
      public
    open import Generic.Linear.Syntax.Interpretation.Map Ty 0-poSemiring
      public
    open import Generic.Linear.Syntax.Term Ty 0-rawPoSemiring public
    open import Generic.Linear.Variable Ty 0-rawPoSemiring public
    open import Generic.Linear.Environment Ty 0-poSemiring public
    open import Generic.Linear.Environment.Categorical Ty 0-poSemiring public
    open import Generic.Linear.Renaming Ty 0-poSemiring public
    open import Generic.Linear.Renaming.Properties Ty 0-poSemiring public
    open import Generic.Linear.Semantics Ty 0-poSemiring public
    open import Generic.Linear.Semantics.Syntactic Ty 0-poSemiring public

  module WithPoSemiring (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ) where

    open PoSemiring poSemiring renaming (Carrier to Ann)

    open import Generic.Linear.Operations rawPoSemiring
    open import Generic.Linear.Algebra poSemiring
    open import Generic.Linear.Syntax Ty Ann
    open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring
    open import Generic.Linear.Syntax.Interpretation.Map Ty poSemiring
    open import Generic.Linear.Syntax.Term Ty rawPoSemiring
    open import Generic.Linear.Variable Ty rawPoSemiring
    open import Generic.Linear.Environment Ty poSemiring
    open import Generic.Linear.Renaming Ty poSemiring
    open import Generic.Linear.Renaming.Properties Ty poSemiring
    open import Generic.Linear.Semantics Ty poSemiring

    uCtx : Ctx → U.Ctx
    uCtx (ctx P γ) = U.ctx _ γ

    uPremises : Premises → U.Premises
    uPremises ⟨ Γ `⊢ A ⟩ = U.⟨ uCtx Γ `⊢ A ⟩
    uPremises `⊤ = U.`⊤
    uPremises `ℑ = U.`ℑ
    uPremises (ps `∧ qs) = uPremises ps U.`∧ uPremises qs
    uPremises (ps `✴ qs) = uPremises ps U.`✴ uPremises qs
    uPremises (r `· ps) = _ U.`· uPremises ps
    uPremises (`□ ps) = U.`□ (uPremises ps)
    uRule : Rule → U.Rule
    uRule (ps =⇒ A) = uPremises ps U.=⇒ A
    uSystem : System → U.System
    uSystem (L ▹ rs) = L U.▹ λ l → uRule (rs l)

    open import Category.Functor
    open import Category.Monad
    open import Data.Bool.Extra
    open import Data.List.Categorical
    open RawFunctor (functor {0ℓ}) using (_<$>_)
    open RawMonad (monad {0ℓ}) using (pure; _>>=_) renaming (_⊛_ to _<*>_)
    open import Data.LTree
    open import Data.LTree.Vector as V hiding ([]; [_]; _++_)
    open import Data.Product as × hiding (_<*>_)
    open import Data.Product.Relation.Binary.Pointwise.NonDependent as ×
    open import Data.Wrap
    open import Function.Base using (_∘_; _$_)
    open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
    open import Relation.Nary
    open import Relation.Unary.Bunched
    open BunchedDuplicable
    open import Size

    pattern uvar i = U.`var (U.lvar i ≡.refl _)




    record NonDetInverses : Set where
      field
        0#⁻¹ : (r : Ann) → List (r ≤ 0#)
        +⁻¹ : (r : Ann) → List (∃ \ ((p , q) : _ × _) → r ≤ p + q)
        1#⁻¹ : (r : Ann) → List (r ≤ 1#)
        *⁻¹ : (r q : Ann) → List (∃ \ p → q ≤ r * p)



        rep : (r : Ann) → List (Dup _≤_ (_≤ 0#) (λ x y z → x ≤ y + z) (λ _ → ⊤) r)



    module WithInverses (invs : NonDetInverses) where

      open NonDetInverses invs

      0*⁻¹ : ∀ {s} (R : Vector Ann s) → List (R ≤0*)
      0*⁻¹ {[-]} R = (| [_]ₙ (0#⁻¹ (R here)) |)
      0*⁻¹ {ε} R = (| []ₙ |)
      0*⁻¹ {s <+> t} R = (| _++ₙ_ (0*⁻¹ (R ∘ ↙)) (0*⁻¹ (R ∘ ↘)) |)

      +*⁻¹ : ∀ {s} (R : Vector Ann s) →
             List (∃ \ ((P , Q) : _ × _) → R ≤[ P +* Q ])
      +*⁻¹ {[-]} R = (| (×.map (×.map V.[_] V.[_]) [_]ₙ) (+⁻¹ (R here)) |)
      +*⁻¹ {ε} R = (| ((V.[] , V.[]) , []ₙ) |)
      +*⁻¹ {s <+> t} R =
        (| (×.zip (×.zip V._++_ V._++_) _++ₙ_) (+*⁻¹ (R ∘ ↙)) (+*⁻¹ (R ∘ ↘)) |)

      ⟨_∣⁻¹ : ∀ {s} (i : Ptr s) R → List (R ≤* ⟨ i ∣)
      ⟨ here ∣⁻¹ R = (| [_]ₙ (1#⁻¹ (R here)) |)
      ⟨ ↙ i ∣⁻¹ R = (| _++ₙ_ (⟨ i ∣⁻¹ (R ∘ ↙)) (L.map 0*→≤* (0*⁻¹ (R ∘ ↘))) |)
      ⟨ ↘ i ∣⁻¹ R = (| _++ₙ_ (L.map 0*→≤* (0*⁻¹ (R ∘ ↙))) (⟨ i ∣⁻¹ (R ∘ ↘)) |)

      *ₗ⁻¹ : ∀ {s} r (Q : Vector Ann s) → List (∃ \ P → Q ≤[ r *ₗ P ])
      *ₗ⁻¹ {[-]} r Q = (| (×.map V.[_] [_]ₙ) (*⁻¹ r (Q here)) |)
      *ₗ⁻¹ {ε} r Q = (| (V.[] , []ₙ) |)
      *ₗ⁻¹ {s <+> t} r Q =
        (| (×.zip V._++_ _++ₙ_) (*ₗ⁻¹ r (Q ∘ ↙)) (*ₗ⁻¹ r (Q ∘ ↘)) |)

      rep* : ∀ {s} (R : Vector Ann s) →
        List (Dup _≤*_ _≤0* _≤[_+*_] (λ _ → ⊤) R)
      rep* {[-]} R = do
        □⟨ str , sp0 , sp+ ⟩ _ ← rep (R here)
        pure $ □⟨_,_,_⟩_ {y = V.[ _ ]} [ str ]ₙ [ sp0 ]ₙ [ sp+ ]ₙ _
      rep* {ε} R = pure $ □⟨_,_,_⟩_ {y = V.[]} []ₙ []ₙ []ₙ _
      rep* {s <+> t} R = do
        □⟨ strl , sp0l , sp+l ⟩ _ ← rep* {s} (R ∘ ↙)
        □⟨ strr , sp0r , sp+r ⟩ _ ← rep* {t} (R ∘ ↘)
        pure $ □⟨_,_,_⟩_ {y = _ V.++ _}
          (strl ++ₙ strr) (sp0l ++ₙ sp0r) (sp+l ++ₙ sp+r) _




      𝓒 : System → U.OpenFam _
      𝓒 sys (U.ctx _ γ) A = ∀ R → List ([ sys , ∞ ] ctx R γ ⊢ A)




      lemma-p : ∀ (sys : System) (ps : Premises) {Γ} →
        U.⟦ uPremises ps ⟧p (U.Scope (𝓒 sys)) (uCtx Γ) →
        List (⟦ ps ⟧p (Scope [ sys , ∞ ]_⊢_) Γ)
      lemma-p sys ⟨ ctx Q δ `⊢ A ⟩ {ctx P γ} t = t (P V.++ Q)
      lemma-p sys `⊤ t = (| t |)
      lemma-p sys `ℑ t = (| ℑ⟨_⟩ (0*⁻¹ _) |)
      lemma-p sys (ps `∧ qs) (s , t) =
        (| _,_ (lemma-p sys ps s) (lemma-p sys qs t) |)
      lemma-p sys (ps `✴ qs) {ctx P γ} (s ✴⟨ _ ⟩ t) = do
        ((Pl , Pr) , sp) ← +*⁻¹ P
        (| _✴⟨ sp ⟩_ (lemma-p sys ps s) (lemma-p sys qs t) |)
      lemma-p sys (r `· ps) {ctx P γ} (⟨ _ ⟩· t) = do
        (P′ , sp) ← *ₗ⁻¹ r P
        (| ⟨ sp ⟩·_ (lemma-p sys ps t) |)
      lemma-p sys (`□ ps) {ctx P γ} (□⟨ _ , _ , _ ⟩ t) = do
        (□⟨ str , sp0 , sp+ ⟩ _) ← rep* P
        (| □⟨ str , sp0 , sp+ ⟩_ (lemma-p sys ps t) |)

      lemma-r : ∀ (sys : System) (r : Rule) {A Γ} →
        U.⟦ uRule r ⟧r (U.Scope (𝓒 sys)) (uCtx Γ) A →
        List (⟦ r ⟧r (Scope [ sys , ∞ ]_⊢_) Γ A)
      lemma-r sys (ps =⇒ B) (q , t) = (| (q ,_) (lemma-p sys ps t) |)




      lemma : ∀ (sys : System) {A Γ} →
        U.⟦ uSystem sys ⟧s (U.Scope (𝓒 sys)) (uCtx Γ) A →
        List (⟦ sys ⟧s (Scope [ sys , ∞ ]_⊢_) Γ A)



      lemma sys@(L ▹ rs) (l , t) = (| (l ,_) (lemma-r sys (rs l) t) |)

      open Semantics using (ren^𝓥; ⟦var⟧; ⟦con⟧)
      open [_]_⇒ᵉ_




      elab-sem : ∀ sys → U.Semantics (uSystem sys) U._∋_ (𝓒 sys)
      elab-sem sys .ren^𝓥 = U.ren^∋
      elab-sem sys .⟦var⟧ (U.lvar i q _) R =
        (| `var (| (lvar i q) (⟨ i ∣⁻¹ R) |) |)
      elab-sem sys .⟦con⟧ b R =
        let rb = U.map-s′ (uSystem sys) U.reify b in
        (| `con (lemma sys rb) |)




      elab : ∀ sys {A s} {γ : Vector Ty s} →
             U.[ uSystem sys , ∞ ] U.ctx _ γ ⊢ A →
             ∀ R → List ([ sys , ∞ ] ctx R γ ⊢ A)
      elab sys = semantics U.identity
        where open U.Semantics (elab-sem sys)

      elab-unique :
        ∀ sys {A s} {γ : Vector Ty s} →
        (M : U.[ uSystem sys , ∞ ] U.ctx _ γ ⊢ A) →
        ∀ R → {_ : Lone (elab sys M R)} → [ sys , ∞ ] ctx R γ ⊢ A
      elab-unique sys M R {l} with uM ∷ [] ← elab sys M R = uM
