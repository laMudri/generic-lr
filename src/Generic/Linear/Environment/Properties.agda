{-# OPTIONS --safe --without-K --prop --postfix-projections #-}

open import Algebra.Po
open import Level using (Level; 0ℓ)

module Generic.Linear.Environment.Properties
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring
    renaming (Carrier to Ann; _≤_ to _⊴_; refl to ⊴-refl; trans to ⊴-trans)

  open import Algebra.Relational
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.Product
  open import Relation.Unary as Syn using (IUniversal)
  open import Relation.Unary.Checked
  open import Relation.Unary.Bunched.Checked
  open import Relation.Binary.PropositionalEquality

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Ty Ann hiding ([_]ᶜ)
  open import Generic.Linear.Syntax.Interpretation Ty rawPoSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring
  open import Generic.Linear.Environment Ty poSemiring
  open import Generic.Linear.Renaming Ty poSemiring

  private
    variable
      Γ Δ : Ctx
      ℓ : Level
      _𝓥_ : Scoped ℓ
      A : Ty
      r : Ann

  ren^Env : (∀ {A} → Renameable (_𝓥 A)) → Renameable ([ _𝓥_ ]_⇒ᵉ Γ)
  ren^Env ren^𝓥 ρ ren .M = ρ .M >>LinMor ren .M
  ren^Env ren^𝓥 ρ ren .asLinRel = ρ .asLinRel >>AsLinRel ren .asLinRel
  ren^Env ren^𝓥 ρ ren .sums = ρ .sums , ren .sums
  ren^Env ren^𝓥 ρ ren .lookup (P′∼Q′ , Q′∼R′) v =
    ren^𝓥 (ρ .lookup P′∼Q′ v) record { [_]_⇒ᵉ_ ren; sums = Q′∼R′ }

  module With-psh^𝓥 {ℓ} {_𝓥_ : Scoped ℓ} (psh^𝓥 : IsPresheaf _𝓥_) where

    private open module Dummy {s} = RelLeftSemimodule (Vᴿ s)

    []ᵉ : ∀[ ℑᶜ ⇒ [ _𝓥_ ]_⇒ᵉ []ᶜ ]
    []ᵉ ℑ⟨ sp ⟩ .M = [─]
    []ᵉ ℑ⟨ sp ⟩ .asLinRel = [─]AsLinRel
    []ᵉ ℑ⟨ sp ⟩ .sums = sp
    []ᵉ ℑ⟨ sp ⟩ .lookup _ (lvar (there () _) _ _)

    ++ᵉ : ∀[ [ _𝓥_ ]_⇒ᵉ Γ ✴ᶜ [ _𝓥_ ]_⇒ᵉ Δ ⇒ [ _𝓥_ ]_⇒ᵉ Γ ++ᶜ Δ ]
    ++ᵉ (ρ ✴⟨ sp ⟩ σ) .M = [ ρ .M ─ σ .M ]
    ++ᵉ (ρ ✴⟨ sp ⟩ σ) .asLinRel = [ ρ .asLinRel ─ σ .asLinRel ]AsLinRel
    ++ᵉ (ρ ✴⟨ sp ⟩ σ) .sums = ρ .sums ↘, sp ,↙ σ .sums
    ++ᵉ (ρ ✴⟨ sp ⟩ σ) .lookup (r ↘, r+s ,↙ s) (lvar (↙ i) q b) =
      let br , bs = un++₂ b in
      let v = ρ .lookup r (lvar i q br) in
      psh^𝓥 (+ₘ-identityʳ→ (r+s , σ .asLinRel .linRel .rel-0ₘ (bs , s))) v
    ++ᵉ (ρ ✴⟨ sp ⟩ σ) .lookup (r ↘, r+s ,↙ s) (lvar (↘ i) q b) =
      let br , bs = un++₂ b in
      let v = σ .lookup s (lvar i q bs) in
      psh^𝓥 (+ₘ-identityˡ→ (ρ .asLinRel .linRel .rel-0ₘ (br , r) , r+s)) v

    [-]ᵉ : ∀ {r A} → ∀[ r ·ᶜ _𝓥 A Syn.⇒ [ _𝓥_ ]_⇒ᵉ [ r · A ]ᶜ ]
    [-]ᵉ (⟨_⟩·_ {Q′} sp v) .M = [─ Q′ ─]
    [-]ᵉ (⟨_⟩·_ {Q′} sp v) .asLinRel = [─ Q′ ─]AsLinRel
    [-]ᵉ (⟨ sp ⟩· v) .sums = sp
    [-]ᵉ (⟨ sp ⟩· v) .lookup t (lvar here refl b) =
      psh^𝓥 (*ₘ-identity→ (b .get here , t)) v
