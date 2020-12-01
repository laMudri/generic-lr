{-# OPTIONS --safe --sized-types --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ)
open import Relation.Binary using (Rel)

module Generic.Linear.Example.BidiMuMuTilde where

  open import Algebra.Relational
  open import Data.Empty
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Data.Maybe as M
  open import Data.Product as ×
  open import Data.Product.Relation.Binary.Pointwise.NonDependent as ×PW
    using (×-setoid)
  open import Data.Unit using (⊤; tt)
  open import Function.Base using (id; _∘_; _∘′_; _$_; λ-; _$-; case_of_)
  open import Function.Equality using (_⟶_; _⇨_; _⟨$⟩_; cong)
  open import Size
  open import Relation.Unary
  open import Relation.Unary.Bunched
  open import Relation.Unary.Bunched.Properties
  open import Relation.Binary using (Setoid)
  open import Relation.Binary.Construct.Always as ⊤ using ()
  open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_; subst; subst₂; _≗_)

  data Dir : Set where syn chk : Dir

  data Pol : Set where trm cot : Pol
  neg : Pol → Pol
  neg trm = cot
  neg cot = trm

  module WithSkewSemiring (skewSemiring : SkewSemiring 0ℓ 0ℓ) where

    open SkewSemiring skewSemiring
      renaming (Carrier to Ann
               ; _≤_ to _⊴_
               ; refl to ⊴-refl; trans to ⊴-trans
               )
    open import Generic.Linear.Operations rawSkewSemiring
    open import Generic.Linear.Algebra skewSemiring

    module WithBaseTypes (Base : Pol → Set) where

      infixr 5 _⊗_
      infixr 6 ↕_
      infixl 7 _^⊥

      data Ty : Pol → Set where
        base : ∀ {p} → Base p → Ty p
        _⊗_ : ∀ {p} → (A B : Ty p) → Ty p
        _^⊥ : ∀ {p} (A : Ty p) → Ty (neg p)
        ↕_ : ∀ {p} (A : Ty (neg p)) → Ty p

      tyeq? : ∀ {p} (A B : Ty p) → Maybe (A ≡ B)
      tyeq? A A′ = {!!}

      module Untyped where

        Conc = Maybe (Dir × Pol)

        open import Generic.Linear.Syntax Conc Ann public
        open import Generic.Linear.Syntax.Interpretation Conc rawSkewSemiring
          public
        open import Generic.Linear.Syntax.Interpretation.Map Conc skewSemiring
          public
        open import Generic.Linear.Syntax.Term Conc rawSkewSemiring public
        open import Generic.Linear.Environment Conc rawSkewSemiring public
          renaming (var to ivar)
        open import Generic.Linear.Thinning Conc rawSkewSemiring public
        open _─Env
        open import Generic.Linear.Extend Conc skewSemiring public
        open import Generic.Linear.Thinning.Properties Conc skewSemiring public
        open import Generic.Linear.Environment.Properties Conc skewSemiring
          public
        open import Generic.Linear.Semantics Conc skewSemiring public

        data `Untyped : Set where
          `cut : (p : Pol) → `Untyped
          `μ : (p : Pol) → `Untyped
          `λ : (p : Pol) → `Untyped
          `⟨-,-⟩ `μ⟨-,-⟩ : (p : Pol) → `Untyped
          ann : ∀ {p} (A : Ty p) → `Untyped
          emb : (p : Pol) → `Untyped

        Untyped : System
        Untyped = system `Untyped λ where
          (`cut p) → rule
            (([]ᶜ `⊢ just (syn , p)) `* ([]ᶜ `⊢ just (chk , neg p)))
            nothing
          (`μ p) → rule
            ([ 1# , just (syn , neg p) ]ᶜ `⊢ nothing)
            (just (chk , p))
          (`λ p) → rule
            ([]ᶜ `⊢ just (chk , neg p))
            (just (chk , p))
          (`⟨-,-⟩ p) → rule
            (([]ᶜ `⊢ just (chk , p)) `* ([]ᶜ `⊢ just (chk , p)))
            (just (chk , p))
          (`μ⟨-,-⟩ p) → rule
            (([ 1# , just (syn , neg p) ]ᶜ ++ᶜ
              [ 1# , just (syn , neg p) ]ᶜ) `⊢ nothing)
            (just (chk , p))
          (ann {p} A) → rule
            ([]ᶜ `⊢ just (chk , p))
            (just (syn , p))
          (emb p) → rule
            ([]ᶜ `⊢ just (syn , p))
            (just (chk , p))

        UntypedTm = Tm Untyped ∞

      module Typed where

        data Conc : Set where
          com : Conc
          syn : ∀ {p} (A : Ty p) → Conc
          chk : ∀ {p} (A : Ty p) (q : Pol) → Conc

        open import Generic.Linear.Syntax Conc Ann public
        open import Generic.Linear.Syntax.Interpretation Conc rawSkewSemiring
          public
        open import Generic.Linear.Syntax.Interpretation.Map Conc skewSemiring
          public
        open import Generic.Linear.Syntax.Term Conc rawSkewSemiring public
        open import Generic.Linear.Environment Conc rawSkewSemiring public
          renaming (var to ivar)
        open import Generic.Linear.Thinning Conc rawSkewSemiring public
        open _─Env
        open import Generic.Linear.Extend Conc skewSemiring public
        open import Generic.Linear.Thinning.Properties Conc skewSemiring public
        open import Generic.Linear.Environment.Properties Conc skewSemiring
          public
        open import Generic.Linear.Semantics Conc skewSemiring public

        data `Typed : Set where
          `cut : ∀ {p} (A : Ty p) → `Typed
          `μ : ∀ {p} (A : Ty (neg p)) → `Typed
          `λ : ∀ {p} (A : Ty p) (q : Pol) → `Typed
          `⟨-,-⟩ `μ⟨-,-⟩ : ∀ {p} (A B : Ty p) → `Typed
          `ann : ∀ {p} (A : Ty p) → `Typed
          `emb : ∀ {p} (A : Ty p) → `Typed

        Typed : System
        Typed = system `Typed λ where
          (`cut {p} A) → rule
            (([]ᶜ `⊢ syn A) `* ([]ᶜ `⊢ chk A (neg p)))
            com
          (`μ {p} A) → rule
            ([ 1# , syn A ]ᶜ `⊢ com)
            (chk A p)
          (`λ A q) → rule
            ([]ᶜ `⊢ chk A (neg q))
            (chk (A ^⊥) q)
          (`⟨-,-⟩ {p} A B) → rule
            (([]ᶜ `⊢ chk A p) `* ([]ᶜ `⊢ chk B p))
            (chk (A ⊗ B) p)
          (`μ⟨-,-⟩ {p} A B) → rule
            (([ 1# , syn A ]ᶜ ++ᶜ [ 1# , syn B ]ᶜ) `⊢ com)
            (chk (A ⊗ B) (neg p))
          (`ann {p} A) → rule
            ([]ᶜ `⊢ chk A p)
            (syn A)
          (`emb {p} A) → rule
            ([]ᶜ `⊢ syn A)
            (chk A p)

        TypedTm = Tm Typed ∞

      module Syntax {Conc : Set} {rawSkewSemiring : RawSkewSemiring 0ℓ 0ℓ}
        where
        open import Generic.Linear.Syntax.Term Conc rawSkewSemiring public
          using (`var; `con)
      open Syntax

      open Untyped using (Untyped; UntypedTm)
      open Typed using (Typed; TypedTm)

      Typing : ∀ {s} → Vector Untyped.Conc s → Set
      Typing = Lift₁ (maybe (uncurry λ _ p → Ty p) ⊥)

      ⌞_⌟ : ∀ {s uΓ} → Typing {s} uΓ → Vector Typed.Conc s
      ⌞_⌟ {s} {uΓ} Γ i with uΓ i | Γ .get i
      ... | just (syn , p) | A = Typed.syn A
      ... | just (chk , q) | A = Typed.chk A q

      Elab : ∀ {ℓ} → Typed.Scoped ℓ → ∀ {s uΓ} →
             Typed.Conc → Vector Ann s → Typing {s} uΓ → Set ℓ
      Elab T 𝓙 R Γ = T 𝓙 (Typed.ctx R ⌞ Γ ⌟)

      untyConc : Typed.Conc → Untyped.Conc
      untyConc Typed.com = nothing
      untyConc (Typed.syn {p} A) = just (syn , p)
      untyConc (Typed.chk A q) = just (chk , q)

      untyCtx : Typed.Ctx → Untyped.Ctx
      untyCtx (Typed.ctx R Γ) = Untyped.ctx R (untyConc ∘ Γ)

      data 𝓥 : Untyped.Scoped 0ℓ where
        vr : ∀ {p A RΓ} → Typed.LVar (Typed.syn {p} A) RΓ →
             𝓥 (just (syn , p)) (untyCtx RΓ)

      𝓒′ : Untyped.Conc → Typed.Ctx → Set
      𝓒′ nothing RΓ = TypedTm Typed.com RΓ
      𝓒′ (just (syn , p)) RΓ = ∃ \ A → TypedTm (Typed.syn {p} A) RΓ
      𝓒′ (just (chk , q)) RΓ = ∀ {p} A → TypedTm (Typed.chk {p} A q) RΓ

      𝓒 : Untyped.Scoped _
      𝓒 𝓙 (Untyped.ctx R uΓ) =
        Maybe $ ∀ Γ → untyConc ∘ Γ ≗ uΓ → 𝓒′ 𝓙 (Typed.ctx R Γ)

      open Untyped.Semantics

      tyelab : Untyped.Semantics Untyped 𝓥 𝓒
      tyelab .th^𝓥 = {!!}
      tyelab .var (vr {A = A} {RΓ′} (Typed.lvar i q b)) =
        just λ Γ Γq → A , `var (Typed.lvar i (≡.trans {!Γq i!} q) b)
        -- go {nothing} (Untyped.lvar i eq b) = {!!}
        -- go {just (syn , p)} (Untyped.lvar i eq b) =
        --   _ , `var (Typed.lvar i (lemma eq .proj₂) b)
        --   where
        --   lemma : ∀ {𝓘 p} → untyConc 𝓘 ≡ just (syn , p) →
        --           ∃ \ A → 𝓘 ≡ Typed.syn {p} A
        --   lemma {Typed.syn A} ≡.refl = A , ≡.refl
        -- go {just (chk , q)} (Untyped.lvar i eq b) = {!!}
      tyelab .alg = {!!}

      {-
      synth : ∀ {p s R} Γ → let RΓ = Typed.ctx {s} R Γ in
              Untyped.UntypedTm (just (syn , p)) (untyCtx RΓ) →
              Maybe (∃ \ A → Typed.TypedTm (Typed.syn {p} A) RΓ)
      check : ∀ {p q s R} Γ A → let RΓ = Typed.ctx {s} R Γ in
              Untyped.UntypedTm (just (chk , q)) (untyCtx RΓ) →
              Maybe (Typed.TypedTm (Typed.chk {p} A q) RΓ)

      synth Γ (`var (Untyped.lvar i q b)) =
        just (_ , `var (Typed.lvar i (lemma q .proj₂) b))
        where
        lemma : ∀ {𝓙 p} →
                untyConc 𝓙 ≡ just (syn , p) → ∃ \ A → 𝓙 ≡ Typed.syn {p} A
        lemma {Typed.syn A} ≡.refl = _ , ≡.refl
      synth Γ (`con (Untyped.ann A , q , M)) = M.map {!A ,_!} (check Γ A {!M!})

      check Γ A M = {!!}
      -}

      -- check : ∃₂ Untyped.UntypedTm →
      --         Maybe (∃₂ Typed.TypedTm)
      -- check (_ , _ , `var x) = just (_ , _ , `var {!!})
      -- check (_ , _ , `con x) = {!!}
