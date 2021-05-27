{-# OPTIONS --safe --sized-types --without-K --prop --postfix-projections #-}

open import Algebra.Skew
open import Level using (Level; 0ℓ)

module Generic.Linear.Semantics.Syntactic
  (Ty : Set) (skewSemiring : SkewSemiring 0ℓ 0ℓ)
  where

  open SkewSemiring skewSemiring
    renaming (Carrier to Ann
             ; _≤_ to _⊴_
             ; refl to ⊴-refl; trans to ⊴-trans
             )

  open import Algebra.Skew.Relation
  open import Data.LTree
  open import Data.LTree.Vector hiding ([]ˢ)
  open import Data.LTree.Matrix
  open import Data.Product
  open import Function.Base using (id; _∘_)
  open import Size
  open import Relation.Unary
  open import Relation.Unary.Bunched
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)

  open import Generic.Linear.Operations rawSkewSemiring
  open import Generic.Linear.Algebra skewSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawSkewSemiring
  open import Generic.Linear.Syntax.Interpretation.Map Ty skewSemiring
  open import Generic.Linear.Syntax.Term Ty rawSkewSemiring
  open import Generic.Linear.Environment Ty rawSkewSemiring
    renaming (var to ivar)
  open import Generic.Linear.Thinning Ty rawSkewSemiring
  open _─Env
  open import Generic.Linear.Extend Ty skewSemiring
  open import Generic.Linear.Thinning.Properties Ty skewSemiring
  open import Generic.Linear.Environment.Properties Ty skewSemiring
  open import Generic.Linear.Semantics Ty skewSemiring

  private
    variable
      fl : PremisesFlags
      d : System fl
      A : Ty
      v c : Level
      𝓥 : Scoped v
      𝓒 : Scoped c
      PΓ QΔ RΘ : Ctx

  record Kit (d : System fl) (𝓥 : Scoped v) : Set v where
    field
      th^𝓥 : ∀ {A} → Thinnable (𝓥 A)
      var : ∀ {A} → ∀[ LVar A ⇒ 𝓥 A ]
      trm : ∀ {A} → ∀[ 𝓥 A ⇒ Tm d ∞ A ]

    psh^𝓥 : IsPresheaf 𝓥
    psh^𝓥 = th⇒psh (λ {A} → th^𝓥 {A})

    instance
      leftExtend : LeftExtend 𝓥
      leftExtend .embedVarˡ v = var (embedVarˡ v)
      rightExtend : RightExtend 𝓥
      rightExtend .embedVarʳ v = var (embedVarʳ v)

  open Semantics

  module _ where
    open Kit

    kit→sem : Kit d 𝓥 → Semantics d 𝓥 (Tm d ∞)
    kit→sem K .th^𝓥 = K .th^𝓥
    kit→sem K .var = K .trm
    kit→sem {d = d} K .alg = `con ∘ map-s′ d (reify {{leftExtend K}})

  Ren-Kit : Kit d LVar
  Ren-Kit = record { th^𝓥 = th^LVar ; var = id ; trm = `var }

  Ren : Semantics d LVar (Tm d ∞)
  Ren = kit→sem Ren-Kit

  ren : Thinning PΓ QΔ → Tm d ∞ A PΓ → Tm d ∞ A QΔ
  ren th t = semantics Ren th t

  th^Tm : Thinnable (Tm d ∞ A)
  th^Tm t th = ren th t

  psh^Tm : IsPresheaf (Tm d ∞)
  psh^Tm = th⇒psh (λ {A} → th^Tm {A = A})

  instance
    re^Tm : RightExtend (Tm d ∞)
    re^Tm .embedVarʳ v = `var (embedVarʳ v)

    le^Tm : LeftExtend (Tm d ∞)
    le^Tm .embedVarˡ v = `var (embedVarˡ v)

  Sub-Kit : Kit d (Tm d ∞)
  Sub-Kit = record { th^𝓥 = th^Tm ; var = `var ; trm = id }

  Sub : Semantics d (Tm d ∞) (Tm d ∞)
  Sub = kit→sem Sub-Kit

  Substitution : (d : System fl) (PΓ QΔ : Ctx) → Set
  Substitution d PΓ QΔ = (PΓ ─Env) (Tm d ∞) QΔ

  sub : Substitution d PΓ QΔ → Tm d ∞ A PΓ → Tm d ∞ A QΔ
  sub σ t = semantics Sub σ t

  -- _>>ˢ_ : Substitution d PΓ QΔ → Substitution d QΔ RΘ → Substitution d PΓ RΘ
  -- (ρ >>ˢ σ) .M = ρ .M *ᴹ σ .M
  -- (ρ >>ˢ σ) .sums = {!!}
  -- (ρ >>ˢ σ) .lookup v = psh^Tm {!!} (sub σ (psh^Tm (⊴*-trans (ρ .sums) {!!}) (ρ .lookup v)))

  module WithKit (K : Kit d 𝓥) where
    private
      module K = Kit K

    infix 5 _++ᵏ_

    1ᵏ : (PΓ ─Env) 𝓥 PΓ
    1ᵏ .M = 1ᴹ
    1ᵏ .sums = unrowL₂ (*ᴹ-1ᴹ (row _))
    1ᵏ .lookup v = K.var (record { Var v; basis = ⊴*-refl })

    -- _>>ᵏ_ : (PΓ ─Env) 𝓥 QΔ → (QΔ ─Env) 𝓥 RΘ → (PΓ ─Env) 𝓥 RΘ
    -- (ρ >>ᵏ σ) .M = ρ .M *ᴹ σ .M
    -- (ρ >>ᵏ σ) .sums =
    --   ⊴*-trans {!((*ᴹ-mono ⊴ᴹ-refl (rowL₂ (ρ .sums))))!} (unrowL₂ (*ᴹ-*ᴹ-→ (row _) (ρ .M) (σ .M)))
    -- (ρ >>ᵏ σ) .lookup v = {!semantics (kit→sem K)!}

    []ᵏ : ([]ᶜ ─Env) 𝓥 []ᶜ
    []ᵏ = 1ᵏ

    _++ᵏ_ : ∀ {PΓl QΔl PΓr QΔr} →
      (PΓl ─Env) 𝓥 QΔl → (PΓr ─Env) 𝓥 QΔr → ((PΓl ++ᶜ PΓr) ─Env) 𝓥 (QΔl ++ᶜ QΔr)
    (ρ ++ᵏ σ) .M =
      [ [ ρ .M │  0ᴹ  ]
               ─
        [  0ᴹ  │ σ .M ] ]
    _++ᵏ_ {PΓl = ctx Pl Γl} {PΓr = ctx Pr Γr} ρ σ .sums =
      ⊴*-trans (ρ .sums) (⊴*-trans (+*-identity↘ _)
        (+*-mono ⊴*-refl (unrowL₂ (*ᴹ-0ᴹ (row Pr)))))
      ++₂
      ⊴*-trans (σ .sums) (⊴*-trans (+*-identity↙ _)
        (+*-mono (unrowL₂ (*ᴹ-0ᴹ (row Pl))) ⊴*-refl))
    (ρ ++ᵏ σ) .lookup (ivar (↙ i) q) = K.th^𝓥 (ρ .lookup (ivar i q)) extendʳ
    (ρ ++ᵏ σ) .lookup (ivar (↘ i) q) = K.th^𝓥 (σ .lookup (ivar i q)) extendˡ

    [_·_]ᵏ : ∀ {r s A B} →
      s ⊴ r → 𝓥 A [ 1# · B ]ᶜ → ([ r · A ]ᶜ ─Env) 𝓥 [ s · B ]ᶜ
    [ le · t ]ᵏ .M _ _ = 1#
    [ le · t ]ᵏ .sums .get i = ⊴-trans le (*.identity .proj₂ _)
    [ le · t ]ᵏ .lookup (ivar i refl) = t

  module _ {fl d} where
    open WithKit (Sub-Kit {fl} {d})

    infix 5 _++ˢ_

    1ˢ : Substitution d PΓ PΓ
    1ˢ = 1ᵏ

    []ˢ : Substitution d []ᶜ []ᶜ
    []ˢ = []ᵏ

    _++ˢ_ : ∀ {PΓl QΔl PΓr QΔr} →
      Substitution d PΓl QΔl → Substitution d PΓr QΔr →
      Substitution d (PΓl ++ᶜ PΓr) (QΔl ++ᶜ QΔr)
    _++ˢ_ = _++ᵏ_

    [_·_]ˢ : ∀ {r s A B} →
      s ⊴ r → Tm d ∞ A [ 1# · B ]ᶜ → Substitution d [ r · A ]ᶜ [ s · B ]ᶜ
    [_·_]ˢ = [_·_]ᵏ
