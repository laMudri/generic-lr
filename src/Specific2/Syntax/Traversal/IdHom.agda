{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Skew
open import Level using (0ℓ; _⊔_)

module Specific2.Syntax.Traversal.IdHom (algebra : SkewSemiring 0ℓ 0ℓ) where

  open import Specific2.Syntax.Prelude algebra
  open import Specific2.Syntax Ann _⊴_ 0# _+_ 1# _*_
  open import Algebra.Skew.Construct.Vector
  open import Specific2.Syntax.Traversal {algebra} id-SkewSemiringMor
    public
  open import Generic.Linear.Syntax Ty Ann

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

  LinMap′ : (s t : LTree) → Set
  LinMap′ = LinMap (id-SkewSemiringMor {R = algebra})

  record Env′ {s t} (T : Ctx → Ty → Set) (M : LinMap′ t s)
              (Γ : Vector Ty s) (Δ : Vector Ty t) : Set where
    open SkewLeftSemimoduleMor M using () renaming (apply to _$M)
    open IVar
    field act : ∀ {A} → (j : IVar Δ A) → T (ctx (⟨ j .idx ∣ $M) Γ) A
  open Env′ public

  record DeployedEnv′ (T : Ctx → Ty → Set) (PΓ : Ctx) (QΔ : Ctx) : Set
    where
    open Ctx PΓ renaming (s to γ; Γ to Γ; R to P)
    open Ctx QΔ renaming (s to δ; Γ to Δ; R to Q)
    field
      linMap : LinMap′ δ γ
      env : Env′ T linMap Γ Δ
      compat : Compat linMap P Q
  open DeployedEnv′ public

  Env′⇒Env : ∀ {s t T} {M : LinMap′ t s} {Γ Δ} → Env′ T M Γ Δ → Env T M Γ Δ
  Env′⇒Env {T = T} ρ .act j = subst (T _) (sym hom-id) (ρ .act j)

  Env⇒Env′ : ∀ {s t T} {M : LinMap′ t s} {Γ Δ} → Env T M Γ Δ → Env′ T M Γ Δ
  Env⇒Env′ {T = T} ρ .act j = subst (T _) hom-id (ρ .act j)

  module _ {T} (K : Kit T) where
    trav′ : ∀ {s t} {Γ : Vector Ty  s} {Δ : Vector Ty  t}
                    {P : Vector Ann s} {Q : Vector Ann t}
            {M : LinMap′ t s} {A} →
            Env′ T M Γ Δ → Compat M P Q → Tm (ctx Q Δ) A → Tm (ctx P Γ) A
    trav′ ρ com M = subst (Tm _) hom-id (trav K (Env′⇒Env ρ) com M)

    travD′ : ∀ {PΓ QΔ} → DeployedEnv′ T PΓ QΔ →
             ∀ {A} → Tm QΔ A → Tm PΓ A
    travD′ ρ = trav′ (ρ .env) (ρ .compat)
