{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ; _⊔_)

module Specific2.Syntax.Traversal.IdHom (algebra : SkewSemiring 0ℓ 0ℓ) where

  open import Specific2.Syntax.Prelude algebra
  open import Specific2.Syntax Ann _⊴_ 0# _+_ 1# _*_
  open import Algebra.Skew.Construct.Vector
  open import Specific2.Syntax.Traversal {algebra} id-SkewSemiringMor
  open import Generic.Linear.Syntax

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.Product
  open import Function.Base
  open import Relation.Binary.PropositionalEquality

  record HomId {a} {A : Set a} (theHom : Hom A A) : Set a where
    constructor mk
    field hom-id : ∀ {x} → hom {{theHom}} x ≡ x
  open HomId {{...}} public

  instance
    TyHomId : HomId TyHom
    TyHomId .hom-id = go $-
      where
      go : ∀ A → hom A ≡ A
      go tι = refl
      go tI = refl
      go t⊤ = refl
      go t0 = refl
      go ((r , A) t⊸ B) = cong₂ _t⊸_ (cong (r ,_) (go A)) (go B)
      go ((p , A) t⊗ (q , B)) =
        cong₂ _t⊗_ (cong (p ,_) (go A)) (cong (q ,_) (go B))
      go ((p , A) t⊕ (q , B)) =
        cong₂ _t⊕_ (cong (p ,_) (go A)) (cong (q ,_) (go B))
      go (A t& B) = cong₂ _t&_ (go A) (go B)
      go (t! (r , A)) = cong t! (cong (r ,_) (go A))

  module _ {T} (K : Kit T) where
    trav′ : ∀ {s t} {Γ : Vector Ty  s} {Δ : Vector Ty  t}
                    {P : Vector Ann s} {Q : Vector Ann t}
            {M : LinMap id-SkewSemiringMor t s} {A} →
            Env T M Γ Δ → Compat M P Q → Tm (ctx Q Δ) A → Tm (ctx P Γ) A
    trav′ ρ com M = subst (Tm _) hom-id (trav K ρ com M)
