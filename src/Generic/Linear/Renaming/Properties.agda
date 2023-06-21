{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Po
open import Function.Base using (flip; _∘_)
open import Level using (Level; 0ℓ)
open import Relation.Binary using (Rel; IsPreorder; Reflexive; Transitive)

module Generic.Linear.Renaming.Properties
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring renaming (Carrier to Ann)

  open import Algebra.Relational
  open import Data.Product
  open import Data.Sum
  open import Function.Base using (id)
  open import Function.Extra
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
  open import Relation.Unary

  open import Data.LTree
  open import Data.LTree.Vector

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Environment Ty poSemiring
  open import Generic.Linear.Environment.Properties Ty poSemiring
  open import Generic.Linear.Environment.Categorical Ty poSemiring
  open import Generic.Linear.Renaming Ty poSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring

  private
    variable
      Γ Δ Θ : Ctx
      ℓ : Level
      T : Ctx → Set ℓ
      𝓥 : OpenFam ℓ
      s t u : LTree
      P P′ Q Q′ R : Vector Ann s
      A : Ty

  -- Also, Renameable ⇒ IsPresheaf via subuse-ren
  psh^∋ : IsPresheaf _∋_
  idx (psh^∋ QP lv) = idx lv
  tyq (psh^∋ QP lv) = tyq lv
  basis (psh^∋ QP lv) = ≤*-trans QP (basis lv)

  ren^∋ : Renameable (_∋ A)
  ren^∋ v th = th .lookup (th .fit-here) v

  open With-psh^𝓥 {𝓥 = _∋_} psh^∋

  {-
  -- The rows of a thinning's matrix are a selection of standard basis vectors
  -- (i.e, rows from the identity matrix).
  -- Which rows, exactly, is defined by the action of the thinning (lookup).
  thinning-sub-1ᴹ :
    ∀ {Γ Δ A}
    (th : Renaming Γ Δ) (v : Var A (Ctx.γ Γ)) →
    Ψ th (v .idx) ≤* 1ᴹ (th .lookup v .idx)
  thinning-sub-1ᴹ {ctx {[-]} P γ} {ctx {t} Q δ} th v@(var here q) =
    th .lookup v .basis
  thinning-sub-1ᴹ {Γ} th (var (↙ i) q) =
    thinning-sub-1ᴹ
      {leftᶜ (ctx→sctx Γ)}
      record { Ψ = topᴹ (th .Ψ); fit-here = ≤*-refl; lookup = th .lookup ∘ leftᵛ }
      (var i q)
  thinning-sub-1ᴹ {Γ} th (var (↘ i) q) =
    thinning-sub-1ᴹ
      {rightᶜ (ctx→sctx Γ)}
      record { Ψ = botᴹ (th .Ψ); fit-here = ≤*-refl; lookup = th .lookup ∘ rightᵛ }
      (var i q)
  -}

  identity : Γ ⇒ʳ Γ
  identity = id^Env

  1ʳ = identity

  select : ∀ {Γ Δ Θ : Ctx} → Γ ⇒ʳ Δ → [ 𝓥 ] Θ ⇒ᵉ Γ → [ 𝓥 ] Θ ⇒ᵉ Δ
  select th ρ = postren^Env ρ th

  compose : ∀ {Γ Δ Θ : Ctx} → Γ ⇒ʳ Δ → Δ ⇒ʳ Θ → Γ ⇒ʳ Θ
  compose = postren^Env

  infixr 5 _>>ʳ_
  _>>ʳ_ = compose

  extract : □ʳ T ⊆ T
  extract t = t identity

  duplicate : □ʳ T ⊆ □ʳ (□ʳ T)
  duplicate t ρ σ = t (compose σ ρ)

  ren^□ : Renameable (□ʳ T)
  ren^□ = duplicate

  subuse-ren : ∀ {γ} → P ≤* Q → ctx P γ ⇒ʳ ctx Q γ
  subuse-ren PQ .Ψ = 1ᴿ
  subuse-ren PQ .fit-here = PQ
  subuse-ren PQ .lookup PQ′ v = psh^∋ PQ′ v

  ren⇒psh : (∀ {A} → Renameable ([ 𝓥 ]_⊨ A)) → IsPresheaf 𝓥
  ren⇒psh ren^𝓥 le v = ren^𝓥 v (subuse-ren le)

  {-
  nat^Th : ∀ {s P′ γ t Q δ} →
    _≤* P′ ◇ (λ P → Renaming (ctx {s} P γ) (ctx {t} Q δ)) →
    (λ Q′ → Renaming (ctx P′ γ) (ctx Q′ δ)) ◇ Q ≤*_
  nat^Th {P′ = P′} (PP , th) .middle = unrow (row P′ *ᴹ th .Ψ)
  nat^Th (PP , th) .fst .Ψ = th .Ψ
  nat^Th (PP , th) .fst .fit-here = ≤*-refl
  nat^Th (PP , th) .fst .lookup v = th .lookup v
  nat^Th (PP , th) .snd =
    ≤*-trans (th .fit-here) (unrowL₂ (*ᴹ-mono (rowL₂ PP) ≤ᴹ-refl))
  -}

  open SizedCtx

  ↙ʳ′ : ∀ {s t} {Γ : SizedCtx (s <+> t)} →
    (Γ .use-ctx ∘ ↘) ≤0* → sctx→ctx Γ ⇒ʳ leftᶜ′ Γ
  ↙ʳ′ sp0 .Ψ = [ 1ᴿ │ 0ᴿ ]ᴿ
  ↙ʳ′ sp0 .fit-here = ≤*-refl , sp0
  ↙ʳ′ sp0 .lookup (le , sp0′) v = psh^∋ le v ↙ᵛ sp0′

  ↘ʳ′ : ∀ {s t} {Γ : SizedCtx (s <+> t)} →
    (Γ .use-ctx ∘ ↙) ≤0* → sctx→ctx Γ ⇒ʳ rightᶜ′ Γ
  ↘ʳ′ sp0 .Ψ = [ 0ᴿ │ 1ᴿ ]ᴿ
  ↘ʳ′ sp0 .fit-here = sp0 , ≤*-refl
  ↘ʳ′ sp0 .lookup (sp0′ , le) v = sp0′ ↘ᵛ psh^∋ le v

  ↙ʳ : ∀ {Γ t δ} → Γ ++ᶜ ctx {t} 0* δ ⇒ʳ Γ
  ↙ʳ = ↙ʳ′ 0*-triv

  ↘ʳ : ∀ {s γ Δ} → ctx {s} 0* γ ++ᶜ Δ ⇒ʳ Δ
  ↘ʳ = ↘ʳ′ 0*-triv
