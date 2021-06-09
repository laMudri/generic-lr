{-# OPTIONS --safe --sized-types --without-K --prop --postfix-projections #-}

open import Algebra.Po
open import Level

module Generic.Linear.Semantics.Syntactic
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring
    renaming (Carrier to Ann
             ; _≤_ to _⊴_
             ; ≤-refl to ⊴-refl; ≤-trans to ⊴-trans
             )

  open import Algebra.Po.Relation
  open import Algebra.Relational
  open import Data.LTree
  open import Data.LTree.Vector hiding ([]ˢ)
  open import Data.Product
  open import Data.Wrap renaming ([_] to mk)
  open import Function.Base using (id; _∘_)
  open import Size
  open import Relation.Unary
  open import Relation.Unary.Bunched
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring
  open import Generic.Linear.Syntax.Interpretation.Map Ty poSemiring
  open import Generic.Linear.Syntax.Term Ty rawPoSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Environment Ty poSemiring
  open import Generic.Linear.Thinning Ty poSemiring
  open import Generic.Linear.Extend Ty poSemiring
  open import Generic.Linear.Thinning.Properties Ty poSemiring
  open import Generic.Linear.Environment.Properties Ty poSemiring
  open import Generic.Linear.Semantics Ty poSemiring

  private
    variable
      fl : PremisesFlags
      d : System fl
      A : Ty
      v c : Level
      𝓥 : Scoped v
      𝓒 : Scoped c
      PΓ QΔ RΘ : Ctx

  record Kit (d : System fl) (𝓥 : Scoped v) : Set (suc 0ℓ ⊔ v) where
    field
      th^𝓥 : ∀ {A} → Thinnable (𝓥 A)
      var : ∀ {A} → ∀[ LVar A ⇒ 𝓥 A ]
      trm : ∀ {A} → ∀[ 𝓥 A ⇒ Tm d ∞ A ]

    psh^𝓥 : IsPresheaf 𝓥
    psh^𝓥 = th⇒psh (λ {A} → th^𝓥 {A})

    instance
      flv : FromLVar 𝓥
      flv .fromLVar = var

  open Semantics

  reify : {{FromLVar 𝓥}} → ∀[ Kripke 𝓥 𝓒 RΘ A ⇒ Scope 𝓒 RΘ A ]
  reify b = b .get extendʳ .app✴ (+*-identity↘ _ ++₂ +*-identity↙ _) extendˡ

  module _ where
    open Kit

    kit→sem : Kit d 𝓥 → Semantics d 𝓥 (Tm d ∞)
    kit→sem K .th^𝓥 = K .th^𝓥
    kit→sem K .var = K .trm
    kit→sem {d = d} K .alg = `con ∘ map-s′ d (reify {{flv K}})

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
    flv^Tm : FromLVar (Tm d ∞)
    flv^Tm .fromLVar = `var

  Sub-Kit : Kit d (Tm d ∞)
  Sub-Kit = record { th^𝓥 = th^Tm ; var = `var ; trm = id }

  Sub : Semantics d (Tm d ∞) (Tm d ∞)
  Sub = kit→sem Sub-Kit

  Substitution : (d : System fl) (PΓ QΔ : Ctx) → Set₁
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
    1ᵏ .asLinRel = idAsLinRel
    1ᵏ .sums = ⊴*-refl
    1ᵏ .lookup le (lvar i q b) = K.var (lvar i q (⊴*-trans le b))

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
    (ρ ++ᵏ σ) .asLinRel =
      [ [ ρ .asLinRel │  0AsLinRel  ]AsLinRel
                      ─
        [  0AsLinRel  │ σ .asLinRel ]AsLinRel ]AsLinRel
    _++ᵏ_ {PΓl = ctx Pl Γl} {PΓr = ctx Pr Γr} ρ σ .sums =
      _↘,_,↙_ {left = _ ++ _} {_ ++ _}
        (ρ .sums , ⊴*-refl)
        (+*-identity↘ _ ++₂ +*-identity↙ _)
        (⊴*-refl , σ .sums)
    (ρ ++ᵏ σ) .lookup ((sρ , 0σ) ↘, sp+ ,↙ (0ρ , sσ)) (lvar (↙ i) q b) =
      let bρ , bσ = un++₂ b in
      let sp+ρ , sp+σ = un++₂ sp+ in
      let leρ = +ₘ-identityʳ→ (sp+ρ , 0ρ) in
      let leσ = +ₘ-identity²→
           (0σ ↘, sp+σ ,↙ σ .asLinRel .linRel .rel-0ₘ (bσ , sσ)) in
      K.th^𝓥 (ρ .lookup sρ (lvar i q bρ)) (extendʳ >>ᵗ subuse-th (leρ ++₂ leσ))
      where open module Dummy {s} = RelLeftSemimodule (Vᴿ s)
    (ρ ++ᵏ σ) .lookup ((sρ , 0σ) ↘, sp+ ,↙ (0ρ , sσ)) (lvar (↘ i) q b) =
      let bρ , bσ = un++₂ b in
      let sp+ρ , sp+σ = un++₂ sp+ in
      let leρ = +ₘ-identity²→
           (ρ .asLinRel .linRel .rel-0ₘ (bρ , sρ) ↘, sp+ρ ,↙ 0ρ) in
      let leσ = +ₘ-identityˡ→ (0σ , sp+σ) in
      K.th^𝓥 (σ .lookup sσ (lvar i q bσ)) (extendˡ >>ᵗ subuse-th (leρ ++₂ leσ))
      where open module Dummy {s} = RelLeftSemimodule (Vᴿ s)

    [_·_]ᵏ : ∀ {r s A B} →
      s ⊴ r → 𝓥 A [ 1# · B ]ᶜ → ([ r · A ]ᶜ ─Env) 𝓥 [ s · B ]ᶜ
    [ le · t ]ᵏ .M = [─ [ 1# ] ─]
    [ le · t ]ᵏ .asLinRel = [─ [ 1# ] ─]AsLinRel
    [ le · t ]ᵏ .sums = [ ⊴-trans le (*.identity .proj₂ _) ]₂
    [ le · t ]ᵏ .lookup r (lvar here refl b) =
      K.th^𝓥 t
        (subuse-th [
          ⊴-trans (r .get here)
            (⊴-trans (*-monoˡ (b .get here)) (*.identity .proj₁ _))
        ]₂)

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
