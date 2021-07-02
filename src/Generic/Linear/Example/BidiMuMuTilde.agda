{-# OPTIONS --safe --sized-types --without-K --postfix-projections --prop #-}

open import Algebra.Po
open import Level using (0ℓ)
open import Relation.Binary using (Rel)

module Generic.Linear.Example.BidiMuMuTilde where

  open import Algebra.Relational
  open import Data.Bool
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
  open import Proposition
  open import Size
  open import Relation.Unary
  open import Relation.Unary.Bunched
  open import Relation.Unary.Bunched.Properties
  open import Relation.Binary using (Setoid)
  open import Relation.Binary.Construct.Always as ⊤ using ()
  open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_; subst; subst₂; _≗_)

  open import Generic.Linear.Syntax.Core

  data Dir : Set where syn chk : Dir

  data Pol : Set where trm cot : Pol
  neg : Pol → Pol
  neg trm = cot
  neg cot = trm

  flags : PremisesFlags
  flags = record noPremisesFlags { Has-✴ = ⊤ᴾ }

  module WithPoSemiring (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ) where

    open PoSemiring poSemiring
      renaming (Carrier to Ann
               ; _≤_ to _⊴_
               ; refl to ⊴-refl; trans to ⊴-trans
               )
    open import Generic.Linear.Operations rawPoSemiring
    open import Generic.Linear.Algebra poSemiring

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
        open import Generic.Linear.Syntax.Interpretation Conc rawPoSemiring
          public
        open import Generic.Linear.Syntax.Interpretation.Map Conc poSemiring
          public
        open import Generic.Linear.Syntax.Term Conc rawPoSemiring public
        open import Generic.Linear.Variable Conc rawPoSemiring public
        open import Generic.Linear.Environment Conc poSemiring public
        open import Generic.Linear.Renaming Conc poSemiring public
        open [_]_⇒ᵉ_
        open import Generic.Linear.Extend Conc poSemiring public
        open import Generic.Linear.Renaming.Properties Conc poSemiring public
        open import Generic.Linear.Environment.Properties Conc poSemiring
          public
        open import Generic.Linear.Semantics Conc poSemiring public

        data `Untyped : Set where
          `cut : (p : Pol) → `Untyped
          `μ : (p : Pol) → `Untyped
          `λ : (p : Pol) → `Untyped
          `⟨-,-⟩ `μ⟨-,-⟩ : (p : Pol) → `Untyped
          ann : ∀ {p} (A : Ty p) → `Untyped
          emb : (p : Pol) → `Untyped

        Untyped : System flags
        Untyped = `Untyped ▹ λ where
          (`cut p) →
            ⟨ []ᶜ `⊢ just (syn , p) ⟩ `✴ ⟨ []ᶜ `⊢ just (chk , neg p) ⟩
            =⇒ nothing
          (`μ p) →
            ⟨ [ 1# , just (syn , neg p) ]ᶜ `⊢ nothing ⟩
            =⇒ just (chk , p)
          (`λ p) →
            ⟨ []ᶜ `⊢ just (chk , neg p) ⟩
            =⇒ just (chk , p)
          (`⟨-,-⟩ p) →
            ⟨ []ᶜ `⊢ just (chk , p) ⟩ `✴ ⟨ []ᶜ `⊢ just (chk , p) ⟩
            =⇒ just (chk , p)
          (`μ⟨-,-⟩ p) →
            ⟨ [ 1# , just (syn , neg p) ]ᶜ ++ᶜ [ 1# , just (syn , neg p) ]ᶜ
              `⊢ nothing ⟩
            =⇒ just (chk , p)
          (ann {p} A) →
            ⟨ []ᶜ `⊢ just (chk , p) ⟩
            =⇒ just (syn , p)
          (emb p) →
            ⟨ []ᶜ `⊢ just (syn , p) ⟩
            =⇒ just (chk , p)

        UntypedTm = [ Untyped , ∞ ]_⊢_

      module Typed where

        data Conc : Set where
          com : Conc
          syn : ∀ {p} (A : Ty p) → Conc
          chk : ∀ {p} (A : Ty p) (q : Pol) → Conc

        open import Generic.Linear.Syntax Conc Ann public
        open import Generic.Linear.Syntax.Interpretation Conc rawPoSemiring
          public
        open import Generic.Linear.Syntax.Interpretation.Map Conc poSemiring
          public
        open import Generic.Linear.Syntax.Term Conc rawPoSemiring public
        open import Generic.Linear.Variable Conc rawPoSemiring public
        open import Generic.Linear.Environment Conc poSemiring public
        open import Generic.Linear.Renaming Conc poSemiring public
        open [_]_⇒ᵉ_
        open import Generic.Linear.Extend Conc poSemiring public
        open import Generic.Linear.Renaming.Properties Conc poSemiring public
        open import Generic.Linear.Environment.Properties Conc poSemiring
          public
        open import Generic.Linear.Semantics Conc poSemiring public

        data `Typed : Set where
          `cut : ∀ {p} (A : Ty p) → `Typed
          `μ : ∀ {p} (A : Ty (neg p)) → `Typed
          `λ : ∀ {p} (A : Ty p) (q : Pol) → `Typed
          `⟨-,-⟩ `μ⟨-,-⟩ : ∀ {p} (A B : Ty p) → `Typed
          `ann : ∀ {p} (A : Ty p) → `Typed
          `emb : ∀ {p} (A : Ty p) → `Typed

        Typed : System flags
        Typed = `Typed ▹ λ where
          (`cut {p} A) →
            ⟨ []ᶜ `⊢ syn A ⟩ `✴ ⟨ []ᶜ `⊢ chk A (neg p) ⟩
            =⇒ com
          (`μ {p} A) →
            ⟨ [ 1# , syn A ]ᶜ `⊢ com ⟩
            =⇒ chk A p
          (`λ A q) →
            ⟨ []ᶜ `⊢ chk A (neg q) ⟩
            =⇒ chk (A ^⊥) q
          (`⟨-,-⟩ {p} A B) →
            ⟨ []ᶜ `⊢ chk A p ⟩ `✴ ⟨ []ᶜ `⊢ chk B p ⟩
            =⇒ chk (A ⊗ B) p
          (`μ⟨-,-⟩ {p} A B) →
            ⟨ [ 1# , syn A ]ᶜ ++ᶜ [ 1# , syn B ]ᶜ `⊢ com ⟩
            =⇒ chk (A ⊗ B) (neg p)
          (`ann {p} A) →
            ⟨ []ᶜ `⊢ chk A p ⟩
            =⇒ syn A
          (`emb {p} A) →
            ⟨ []ᶜ `⊢ syn A ⟩
            =⇒ chk A p

        TypedTm = [ Typed , ∞ ]_⊢_

      module Syntax {Conc : Set} {rawPoSemiring : RawPoSemiring 0ℓ 0ℓ 0ℓ}
        where
        open import Generic.Linear.Syntax.Term Conc rawPoSemiring public
          using (`var; `con)
      open Syntax

      open Untyped using (Untyped; UntypedTm)
      open Typed using (Typed; TypedTm)

      Typing : ∀ {s} → Vector Untyped.Conc s → Set
      Typing = Lift₁ (maybe (uncurry λ _ p → Ty p) ⊥)

      ⌞_⌟ : ∀ {s uγ} → Typing {s} uγ → Vector Typed.Conc s
      ⌞_⌟ {s} {uγ} γ i with uγ i | γ .get i
      ... | just (syn , p) | A = Typed.syn A
      ... | just (chk , q) | A = Typed.chk A q

      Elab : ∀ {ℓ} → Typed.Scoped ℓ → ∀ {s uγ} →
             Typed.Conc → Vector Ann s → Typing {s} uγ → Set ℓ
      Elab T 𝓙 R γ = T (Typed.ctx R ⌞ γ ⌟) 𝓙

      untyConc : Typed.Conc → Untyped.Conc
      untyConc Typed.com = nothing
      untyConc (Typed.syn {p} A) = just (syn , p)
      untyConc (Typed.chk A q) = just (chk , q)

      untyCtx : Typed.Ctx → Untyped.Ctx
      untyCtx (Typed.ctx R γ) = Untyped.ctx R (untyConc ∘ γ)

      data 𝓥 : Untyped.Scoped 0ℓ where
        vr : ∀ {p A Γ} → Γ Typed.∋ Typed.syn {p} A →
             𝓥 (untyCtx Γ) (just (syn , p))

      𝓒′ : Typed.Ctx → Untyped.Conc → Set
      𝓒′ Γ nothing = TypedTm Γ Typed.com
      𝓒′ Γ (just (syn , p)) = ∃ \ A → TypedTm Γ (Typed.syn {p} A)
      𝓒′ Γ (just (chk , q)) = ∀ {p} A → TypedTm Γ (Typed.chk {p} A q)

      𝓒 : Untyped.Scoped _
      𝓒 (Untyped.ctx R uγ) 𝓙 =
        Maybe $ ∀ γ → untyConc ∘ γ ≗ uγ → 𝓒′ (Typed.ctx R γ) 𝓙

      open Untyped.Semantics

      tyelab : Untyped.Semantics Untyped 𝓥 𝓒
      tyelab .ren^𝓥 = {!!}
      tyelab .var (vr {A = A} {Γ′} (Typed.lvar i q b)) =
        just λ γ γq → A , `var (Typed.lvar i (≡.trans {!γq i!} q) b)
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
      synth : ∀ {p s R} γ → let Γ = Typed.ctx {s} R γ in
              Untyped.UntypedTm (just (syn , p)) (untyCtx Γ) →
              Maybe (∃ \ A → Typed.TypedTm (Typed.syn {p} A) Γ)
      check : ∀ {p q s R} γ A → let Γ = Typed.ctx {s} R γ in
              Untyped.UntypedTm (just (chk , q)) (untyCtx Γ) →
              Maybe (Typed.TypedTm (Typed.chk {p} A q) Γ)

      synth γ (`var (Untyped.lvar i q b)) =
        just (_ , `var (Typed.lvar i (lemma q .proj₂) b))
        where
        lemma : ∀ {𝓙 p} →
                untyConc 𝓙 ≡ just (syn , p) → ∃ \ A → 𝓙 ≡ Typed.syn {p} A
        lemma {Typed.syn A} ≡.refl = _ , ≡.refl
      synth γ (`con (Untyped.ann A , q , M)) = M.map {!A ,_!} (check γ A {!M!})

      check γ A M = {!!}
      -}

      -- check : ∃₂ Untyped.UntypedTm →
      --         Maybe (∃₂ Typed.TypedTm)
      -- check (_ , _ , `var x) = just (_ , _ , `var {!!})
      -- check (_ , _ , `con x) = {!!}
