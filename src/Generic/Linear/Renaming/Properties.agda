{-# OPTIONS --safe --without-K --prop --postfix-projections #-}

open import Algebra.Po
open import Function.Base using (flip; _∘_)
open import Level using (Level; 0ℓ)
open import Relation.Binary using (Rel; IsPreorder; Reflexive; Transitive)

module Generic.Linear.Renaming.Properties
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring
    renaming (Carrier to Ann; _≤_ to _⊴_; refl to ⊴-refl; trans to ⊴-trans)

  open import Algebra.Relational
  open import Data.Product
  open import Data.Sum
  open import Function.Extra
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
  open import Relation.Unary

  open import Data.LTree
  open import Data.LTree.Vector

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Environment Ty poSemiring
  open import Generic.Linear.Renaming Ty poSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring
  -- open import Generic.Linear.Extend Ty poSemiring

  private
    variable
      Γ Δ Θ : Ctx
      ℓ : Level
      T : Ctx → Set ℓ
      𝓥 : Scoped ℓ
      s t u : LTree
      P P′ Q Q′ R : Vector Ann s
      A : Ty

  -- Also, Renameable ⇒ IsPresheaf via subuse-ren
  psh^∋ : IsPresheaf _∋_
  idx (psh^∋ QP lv) = idx lv
  tyq (psh^∋ QP lv) = tyq lv
  basis (psh^∋ QP lv) = ⊴*-trans QP (basis lv)

  ren^∋ : Renameable (_∋ A)
  ren^∋ v th = th .lookup (th .sums) v

  {-
  -- The rows of a thinning's matrix are a selection of standard basis vectors
  -- (i.e, rows from the identity matrix).
  -- Which rows, exactly, is defined by the action of the thinning (lookup).
  thinning-sub-1ᴹ :
    ∀ {Γ Δ A}
    (th : Renaming Γ Δ) (v : Var A (Ctx.γ Γ)) →
    M th (v .idx) ⊴* 1ᴹ (th .lookup v .idx)
  thinning-sub-1ᴹ {ctx {[-]} P γ} {ctx {t} Q δ} th v@(var here q) =
    th .lookup v .basis
  thinning-sub-1ᴹ {Γ} th (var (↙ i) q) =
    thinning-sub-1ᴹ
      {leftᶜ (ctx→sctx Γ)}
      record { M = topᴹ (th .M); sums = ⊴*-refl; lookup = th .lookup ∘ leftᵛ }
      (var i q)
  thinning-sub-1ᴹ {Γ} th (var (↘ i) q) =
    thinning-sub-1ᴹ
      {rightᶜ (ctx→sctx Γ)}
      record { M = botᴹ (th .M); sums = ⊴*-refl; lookup = th .lookup ∘ rightᵛ }
      (var i q)
  -}

  identity : Γ ⇒ʳ Γ
  identity .M = idLinMor
  identity .asLinRel = idAsLinRel
  identity .sums = ⊴*-refl
  identity .lookup le v = record { _∋_ v; basis = ⊴*-trans le (v .basis) }

  1ʳ = identity

  select : ∀ {Γ Δ Θ : Ctx} → Γ ⇒ʳ Δ → [ 𝓥 ] Θ ⇒ᵉ Γ → [ 𝓥 ] Θ ⇒ᵉ Δ
  select th ρ .M = th .M >>LinMor ρ .M
  select th ρ .asLinRel = th .asLinRel >>AsLinRel ρ .asLinRel
  select th ρ .sums = th .sums , ρ .sums
  select th ρ .lookup (th-r , ρ-r) v = ρ .lookup ρ-r (th .lookup th-r v)

  compose : ∀ {Γ Δ Θ : Ctx} → Δ ⇒ʳ Θ → Γ ⇒ʳ Δ → Γ ⇒ʳ Θ
  compose th ph = select th ph

  -- TODO: this is now the wrong way round.
  infixr 5 _>>ʳ_
  _>>ʳ_ = compose

  extract : ∀[ □ʳ T ⇒ T ]
  extract t = t identity

  duplicate : ∀[ □ʳ T ⇒ □ʳ (□ʳ T) ]
  duplicate t ρ σ = t (compose ρ σ)

  ren^□ : Renameable (□ʳ T)
  ren^□ = duplicate

  subuse-ren : ∀ {γ} → P ⊴* Q → ctx P γ ⇒ʳ ctx Q γ
  subuse-ren PQ .M = idLinMor
  subuse-ren PQ .asLinRel = idAsLinRel
  subuse-ren PQ .sums = PQ
  subuse-ren PQ .lookup PQ′ v = psh^∋ PQ′ v

  ren⇒psh : (∀ {A} → Renameable (_⟨ 𝓥 ⟩⊢ A)) → IsPresheaf 𝓥
  ren⇒psh ren^𝓥 le v = ren^𝓥 v (subuse-ren le)

  {-
  nat^Th : ∀ {s P′ γ t Q δ} →
    _⊴* P′ ◇ (λ P → Renaming (ctx {s} P γ) (ctx {t} Q δ)) →
    (λ Q′ → Renaming (ctx P′ γ) (ctx Q′ δ)) ◇ Q ⊴*_
  nat^Th {P′ = P′} (PP , th) .middle = unrow (row P′ *ᴹ th .M)
  nat^Th (PP , th) .fst .M = th .M
  nat^Th (PP , th) .fst .sums = ⊴*-refl
  nat^Th (PP , th) .fst .lookup v = th .lookup v
  nat^Th (PP , th) .snd =
    ⊴*-trans (th .sums) (unrowL₂ (*ᴹ-mono (rowL₂ PP) ⊴ᴹ-refl))
  -}
