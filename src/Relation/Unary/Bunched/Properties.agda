{-# OPTIONS --safe --without-K --postfix-projections #-}

-- PRINCIPLE: properties should be usable with both synthesising and checked
-- level versions of the bunched combinators.

module Relation.Unary.Bunched.Properties where

  open import Algebra.Relational
  open import Data.Product
  open import Level
  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary
  open import Relation.Unary.Bunched using
    (module BunchedUnit; module BunchedConjunction; module BunchedScaling)

  module BunchedCommutativeMonoid
    {c ℓ} (skewCommutativeRelMonoid : SkewCommutativeRelMonoid c ℓ)
    where

    open SkewCommutativeRelMonoid skewCommutativeRelMonoid
    open BunchedUnit _≤ε
    open BunchedConjunction _≤[_∙_]

    module _ {t} {T : Pred Carrier t} {v : Level} where

      1-✴→ : ∀[ ✴1 {v} ✴ T ⇒ T ]
      1-✴→ (✴1⟨ sp0 ⟩ ✴⟨ sp+ ⟩ t) = subst T (identityˡ→ (sp0 , sp+)) t

      1-✴← : ∀[ T ⇒ ✴1 {v} ✴ T ]
      1-✴← t = let sp0 , sp+ = identityˡ← refl in ✴1⟨ sp0 ⟩ ✴⟨ sp+ ⟩ t

      ✴-1→ : ∀[ T ✴ ✴1 {v} ⇒ T ]
      ✴-1→ (t ✴⟨ sp+ ⟩ ✴1⟨ sp0 ⟩) = subst T (identityʳ→ (sp+ , sp0)) t

      ✴-1← : ∀[ T ⇒ T ✴ ✴1 {v} ]
      ✴-1← t = let sp+ , sp0 = identityʳ← refl in t ✴⟨ sp+ ⟩ ✴1⟨ sp0 ⟩

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
