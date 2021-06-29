{-# OPTIONS --safe --without-K --postfix-projections #-}

-- PRINCIPLE: properties should be usable with both synthesising and checked
-- level versions of the bunched combinators.

module Relation.Unary.Bunched.Properties where

  open import Algebra.Skew using (Proset)
  open import Algebra.Relational
  open import Data.Product
  open import Level
  open import Relation.Unary
  open import Relation.Unary.Bunched using
    ( module BunchedOrder; module BunchedUnit
    ; module BunchedConjunction; module BunchedScaling
    )

  module BunchedProset {c ℓ} (proset : Proset c ℓ) where

    open Proset proset
    open BunchedOrder _≤_

    module _ {t} {T : Pred Carrier t} where

      pure-◇ : ∀[ T ⇒ ◇ T ]
      pure-◇ t = ◇⟨ refl ⟩ t

      join-◇ : ∀[ ◇ (◇ T) ⇒ ◇ T ]
      join-◇ (◇⟨ xy ⟩ (◇⟨ yz ⟩ t)) = ◇⟨ trans xy yz ⟩ t

      alg-◇ : (psh^T : ∀ {x y} → x ≤ y → T y → T x) → ∀[ ◇ T ⇒ T ]
      alg-◇ psh^T (◇⟨ xy ⟩ t) = psh^T xy t

  module BunchedCommutativeMonoid
    {c ℓ} (commutativeRelMonoid : CommutativeRelMonoid c ℓ)
    where

    open CommutativeRelMonoid commutativeRelMonoid
    open BunchedUnit _≤ε
    open BunchedConjunction _≤[_∙_]
    open BunchedOrder _≤_

    open BunchedProset proset public

    module _ {t} {T : Pred Carrier t} {v : Level} where

      1-✴→ : ∀[ ℑ {v} ✴ T ⇒ ◇ T ]
      1-✴→ (ℑ⟨ sp0 ⟩ ✴⟨ sp+ ⟩ t) = ◇⟨ identityˡ→ (sp0 , sp+) ⟩ t

      1-✴← : ∀[ ◇ T ⇒ ℑ {v} ✴ T ]
      1-✴← (◇⟨ sub ⟩ t) = let sp0 , sp+ = identityˡ← sub in ℑ⟨ sp0 ⟩ ✴⟨ sp+ ⟩ t

      ✴-1→ : ∀[ T ✴ ℑ {v} ⇒ ◇ T ]
      ✴-1→ (t ✴⟨ sp+ ⟩ ℑ⟨ sp0 ⟩) = ◇⟨ identityʳ→ (sp+ , sp0) ⟩ t

      ✴-1← : ∀[ ◇ T ⇒ T ✴ ℑ {v} ]
      ✴-1← (◇⟨ sub ⟩ t) = let sp+ , sp0 = identityʳ← sub in t ✴⟨ sp+ ⟩ ℑ⟨ sp0 ⟩

    module _ {t u v : Level} where

      1✴1→ : ∀[ ℑ {t} ✴ ℑ {u} ⇒ ℑ {v} ]
      1✴1→ (ℑ⟨ spl ⟩ ✴⟨ sp+ ⟩ ℑ⟨ spr ⟩) = ℑ⟨ identity²→ (spl ↘, sp+ ,↙ spr) ⟩

      1✴1← : ∀[ ℑ {v} ⇒ ℑ {t} ✴ ℑ {u} ]
      1✴1← ℑ⟨ sp0 ⟩ =
        let spl ↘, sp+ ,↙ spr = identity²← sp0 in
        ℑ⟨ spl ⟩ ✴⟨ sp+ ⟩ ℑ⟨ spr ⟩

    module _
      {t u v} {T : Pred Carrier t} {U : Pred Carrier u} {V : Pred Carrier v}
      where

      ✴-✴→ : ∀[ (T ✴ U) ✴ V ⇒ T ✴ (U ✴ V) ]
      ✴-✴→ ((t ✴⟨ spl ⟩ u) ✴⟨ sp ⟩ v) =
        let sp′ , spr = assoc→ (spl , sp) in
        t ✴⟨ sp′ ⟩ (u ✴⟨ spr ⟩ v)

      ✴-✴← : ∀[ T ✴ (U ✴ V) ⇒ (T ✴ U) ✴ V ]
      ✴-✴← (t ✴⟨ sp ⟩ (u ✴⟨ spr ⟩ v)) =
        let spl , sp′ = assoc← (sp , spr) in
        (t ✴⟨ spl ⟩ u) ✴⟨ sp′ ⟩ v

      curry-✴ : ∀[ (T ✴ U ─✴ V) ⇒ (T ─✴ U ─✴ V) ]
      curry-✴ f .app✴ sp0 t .app✴ sp1 u =
        let sp0′ , sp1′ = assoc→ (sp0 , sp1) in
        f .app✴ sp0′ (t ✴⟨ sp1′ ⟩ u)

      uncurry-✴ : ∀[ (T ─✴ U ─✴ V) ⇒ (T ✴ U ─✴ V) ]
      uncurry-✴ f .app✴ sp0 (t ✴⟨ sp1 ⟩ u) =
        let sp0′ , sp1′ = assoc← (sp0 , sp1) in
        f .app✴ sp0′ t .app✴ sp1′ u

    module _ {t u} {T : Pred Carrier t} {U : Pred Carrier u} where

      comm-✴ : ∀[ T ✴ U ⇒ U ✴ T ]
      comm-✴ (t ✴⟨ sp ⟩ u) = u ✴⟨ comm sp ⟩ t

      eval✴ : ∀[ (T ─✴ U) ✴ T ⇒ U ]
      eval✴ (f ✴⟨ sp ⟩ x) = f .app✴ sp x

    module _
      {t u v} {T : Pred Carrier t} {U : Pred Carrier u} {V : Pred Carrier v}
      where

      ∘✴ : ∀[ (U ─✴ V) ✴ (T ─✴ U) ⇒ (T ─✴ V) ]
      ∘✴ (g ✴⟨ sp0 ⟩ f) .app✴ sp1 x =
        let sp0′ , sp1′ = assoc→ (sp0 , sp1) in
        g .app✴ sp0′ (f .app✴ sp1′ x)

    module _
      {t u v w} {T : Pred Carrier t} {U : Pred Carrier u}
      {V : Pred Carrier v} {W : Pred Carrier w}
      where

      inter-✴ : ∀[ (T ✴ U) ✴ (V ✴ W) ⇒ (T ✴ V) ✴ (U ✴ W) ]
      inter-✴ ((t ✴⟨ spl ⟩ u) ✴⟨ sp ⟩ (v ✴⟨ spr ⟩ w)) =
        let spl′ ↘, sp′ ,↙ spr′ = inter (spl ↘, sp ,↙ spr) in
        (t ✴⟨ spl′ ⟩ v) ✴⟨ sp′ ⟩ (u ✴⟨ spr′ ⟩ w)
