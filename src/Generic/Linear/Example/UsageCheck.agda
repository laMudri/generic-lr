{-# OPTIONS --safe --sized-types --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (Level; 0ℓ; suc)
open import Relation.Binary using (Rel)

module Generic.Linear.Example.UsageCheck
  (Ty : Set) (skewSemiring : SkewSemiring 0ℓ 0ℓ)
  where

  open SkewSemiring skewSemiring
    renaming (Carrier to Ann
             ; _≤_ to _⊴_
             ; refl to ⊴-refl; trans to ⊴-trans
             )

  open import Data.Unit

  module U where

    0-skewSemiring : SkewSemiring 0ℓ 0ℓ
    0-skewSemiring = record
      { proset = record { Carrier = ⊤ ; _≤_ = λ _ _ → ⊤ } }

    0-rawSkewSemiring : RawSkewSemiring 0ℓ 0ℓ
    0-rawSkewSemiring = SkewSemiring.rawSkewSemiring 0-skewSemiring

    open import Generic.Linear.Operations 0-rawSkewSemiring public
    open import Generic.Linear.Algebra 0-skewSemiring public
    open import Generic.Linear.Syntax Ty ⊤ public
    open import Generic.Linear.Syntax.Interpretation Ty 0-rawSkewSemiring
      public
    open import Generic.Linear.Syntax.Interpretation.Map Ty 0-skewSemiring
      public
    open import Generic.Linear.Syntax.Term Ty 0-rawSkewSemiring public
    open import Generic.Linear.Environment Ty 0-rawSkewSemiring public
      renaming (var to ivar)
    open import Generic.Linear.Thinning Ty 0-rawSkewSemiring public
    open import Generic.Linear.Thinning.Properties Ty 0-skewSemiring public
    open _─Env public
    open import Generic.Linear.Extend Ty 0-skewSemiring public
    open import Generic.Linear.Semantics Ty 0-skewSemiring public
    open import Generic.Linear.Semantics.Syntactic Ty 0-skewSemiring public
      using (reify)

  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Algebra skewSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawSkewSemiring
  open import Generic.Linear.Syntax.Interpretation.Map Ty skewSemiring
  open import Generic.Linear.Syntax.Term Ty rawSkewSemiring
  open import Generic.Linear.Environment Ty rawSkewSemiring
    renaming (var to ivar)
  open import Generic.Linear.Thinning Ty rawSkewSemiring
  open import Generic.Linear.Thinning.Properties Ty skewSemiring
  open _─Env
  open import Generic.Linear.Extend Ty skewSemiring
  open import Generic.Linear.Semantics Ty skewSemiring
  open import Generic.Linear.Semantics.Syntactic Ty skewSemiring using (reify)

  uCtx : Ctx → U.Ctx
  uCtx (ctx P Γ) = U.ctx _ Γ

  uPremises : Premises → U.Premises
  uPremises (PΓ `⊢ A) = uCtx PΓ U.`⊢ A
  uPremises `⊤ = U.`⊤
  uPremises `I = U.`I
  uPremises (ps `∧ qs) = uPremises ps U.`∧ uPremises qs
  uPremises (ps `* qs) = uPremises ps U.`* uPremises qs
  uPremises (ρ `· ps) = _ U.`· uPremises ps
  uRule : Rule → U.Rule
  uRule (rule ps A) = U.rule (uPremises ps) A
  uSystem : System → U.System
  uSystem (system L rs) = U.system L λ l → uRule (rs l)

  open import Category.Functor
  -- open import Category.Applicative
  open import Category.Monad
  open import Data.List as L using (List; []; _∷_; [_])
  open import Data.List.Categorical
  open RawFunctor (functor {0ℓ}) using (_<$>_)
  -- open RawApplicative (applicative {0ℓ}) using (pure) renaming (_⊛_ to _<*>_)
  open RawMonad (monad {0ℓ}) using (pure; _>>=_) renaming (_⊛_ to _<*>_)
  -- open import Data.List.Membership.Propositional
  -- open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
  -- open import Data.List.Relation.Unary.Any.Properties as AnyP using ()
  open import Data.LTree
  open import Data.LTree.Vector as V hiding ([]; [_]; _++_)
  open import Data.Product as ×
  open import Data.Product.Relation.Binary.Pointwise.NonDependent as ×
  open import Function.Base using (_∘_)
  -- open import Function.Equality using (Π; _⟨$⟩_)
  -- open import Function.Inverse using (_↔_; Inverse)
  -- open Inverse
  open import Relation.Unary
  open import Relation.Unary.Bunched
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; inspect)
  open import Size

  module WithInverses
    (0#⁻¹ : (r : Ann) → List (r ⊴ 0#))
    (+⁻¹ : (r : Ann) → List (∃ \ ((p , q) : Ann × Ann) → r ⊴ p + q))
    (1#⁻¹ : (r : Ann) → List (r ⊴ 1#))
    (*⁻¹ : (r q : Ann) → List (∃ \ p → q ⊴ r * p))
    where

    0*⁻¹ : ∀ {s} (R : Vector Ann s) → List (R ⊴* 0*)
    0*⁻¹ {[-]} R = (| [_]₂ (0#⁻¹ (R here)) |)
    0*⁻¹ {ε} R = (| []₂ |)
    0*⁻¹ {s <+> t} R = (| _++₂_ (0*⁻¹ (R ∘ ↙)) (0*⁻¹ (R ∘ ↘)) |)

    +*⁻¹ : ∀ {s} (R : Vector Ann s) → List (∃ \ ((P , Q) : _ × _) → R ⊴* P +* Q)
    +*⁻¹ {[-]} R = (| (×.map (×.map V.[_] V.[_]) [_]₂) (+⁻¹ (R here)) |)
    +*⁻¹ {ε} R = (| ((V.[] , V.[]) , []₂) |)
    +*⁻¹ {s <+> t} R =
      (| (×.zip (×.zip V._++_ V._++_) _++₂_) (+*⁻¹ (R ∘ ↙)) (+*⁻¹ (R ∘ ↘)) |)

    ⟨_∣⁻¹ : ∀ {s} (i : Ptr s) R → List (R ⊴* 1ᴹ i)
    ⟨ here ∣⁻¹ R = (| [_]₂ (1#⁻¹ (R here)) |)
    ⟨ ↙ i ∣⁻¹ R = (| _++₂_ (⟨ i ∣⁻¹ (R ∘ ↙)) (0*⁻¹ (R ∘ ↘)) |)
    ⟨ ↘ i ∣⁻¹ R = (| _++₂_ (0*⁻¹ (R ∘ ↙)) (⟨ i ∣⁻¹ (R ∘ ↘)) |)

    *ₗ⁻¹ : ∀ {s} r (Q : Vector Ann s) → List (∃ \ P → Q ⊴* r *ₗ P)
    *ₗ⁻¹ {[-]} r Q = (| (×.map V.[_] [_]₂) (*⁻¹ r (Q here)) |)
    *ₗ⁻¹ {ε} r Q = (| (V.[] , []₂) |)
    *ₗ⁻¹ {s <+> t} r Q =
      (| (×.zip V._++_ _++₂_) (*ₗ⁻¹ r (Q ∘ ↙)) (*ₗ⁻¹ r (Q ∘ ↘)) |)

    lemma-p :
      ∀ (sys : System) (ps : Premises) {PΓ} →
      U.⟦ uPremises ps ⟧p
        (U.Scope λ B (U.ctx _ Δ) → ∀ Q → List (Tm sys ∞ B (ctx Q Δ)))
        (uCtx PΓ) →
      List (⟦ ps ⟧p (Scope (Tm sys ∞)) PΓ)
    lemma-p sys (ctx Q Δ `⊢ A) {ctx P Γ} t = t (P V.++ Q)
    lemma-p sys `⊤ t = (| t |)
    lemma-p sys `I t = (| ✴1⟨_⟩ (0*⁻¹ _) |)
    lemma-p sys (ps `∧ qs) (s , t) =
      (| _,_ (lemma-p sys ps s) (lemma-p sys qs t) |)
    lemma-p sys (ps `* qs) {ctx P Γ} (s ✴⟨ _ ⟩ t) = do
      ((Pl , Pr) , sp) ← +*⁻¹ P
      (| _✴⟨ sp ⟩_ (lemma-p sys ps s) (lemma-p sys qs t) |)
    lemma-p sys (r `· ps) {ctx P Γ} (⟨ _ ⟩· t) = do
      (P′ , sp) ← *ₗ⁻¹ r P
      (| ⟨ sp ⟩·_ (lemma-p sys ps t) |)

    lemma-r :
      ∀ (sys : System) (r : Rule) {A PΓ} →
      U.⟦ uRule r ⟧r
        (U.Scope λ B (U.ctx _ Δ) → ∀ Q → List (Tm sys ∞ B (ctx Q Δ)))
        A (uCtx PΓ) →
      List (⟦ r ⟧r (Scope (Tm sys ∞)) A PΓ)
    lemma-r sys (rule ps B) (q , t) = (| (q ,_) (lemma-p sys ps t) |)

    lemma :
      ∀ (sys : System) {A PΓ} →
      U.⟦ uSystem sys ⟧s
        (U.Scope λ B (U.ctx _ Δ) → ∀ Q → List (Tm sys ∞ B (ctx Q Δ)))
        A (uCtx PΓ) →
      -- U.⟦ uSystem sys ⟧s (U.Scope (U.Tm (uSystem sys) ∞)) A (uCtx PΓ) →
      List (⟦ sys ⟧s (Scope (Tm sys ∞)) A PΓ)
    lemma sys@(system L rs) (l , t) = (| (l ,_) (lemma-r sys (rs l) t) |)

    module _ (sys : System) where

      𝓒 : U.Scoped _
      𝓒 A (U.ctx _ Γ) = ∀ R → List (Tm sys ∞ A (ctx R Γ))

      open Semantics using (th^𝓥; var; alg)

      elab-sem : U.Semantics (uSystem sys) U.LVar 𝓒
      elab-sem .th^𝓥 (U.lvar i q _) th =
        let v = th .U.lookup (U.ivar i q) in
        U.lvar (v .U.idx) (v .U.tyq) _
      elab-sem .var (U.lvar i q _) R =
        (| `var (| (lvar i q) (⟨ i ∣⁻¹ R) |) |)
      elab-sem .alg b R =
        let foo = U.map-s′ (uSystem sys) (U.reify {𝓥 = U.LVar} {𝓒 = 𝓒}) b in
        (| `con (lemma sys foo) |)  -- (sequence-s {{applicative}} sys {!!})

      elab : ∀ {A s} {Γ : Vector Ty s} →
             U.Tm (uSystem sys) ∞ A (U.ctx _ Γ) →
             ∀ R → List (Tm sys ∞ A (ctx R Γ))
      elab = semantics U.identity
        where open U.Semantics elab-sem
