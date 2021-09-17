{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Po
open import Level using (Level; 0ℓ)

module Generic.Linear.Environment.Properties
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring renaming (Carrier to Ann)

  open import Algebra.Relational
  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.Product
  open import Function.Base using (_∘_)
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
  open import Generic.Linear.Environment.Categorical Ty poSemiring
  open import Generic.Linear.Renaming Ty poSemiring

  private
    variable
      Γ Δ : Ctx
      A : Ty
      r : Ann

  ren^Env : ∀ {v} {_𝓥_ : OpenFam v} →
    (∀ {A} → Renameable (_𝓥 A)) → (∀ {Δ} → Renameable ([ _𝓥_ ]_⇒ᵉ Δ))
  ren^Env {_𝓥_ = 𝓥} ren^𝓥 ρ ren = >>^Env ren ρ
    where
    instance
      composeEnv : ComposeEnv _∋_ 𝓥 𝓥
      composeEnv .lift ren′ r v = ren^𝓥 v (record { [_]_⇒ᵉ_ ren′; sums = r })

  module With-psh^𝓥 {ℓ} {_𝓥_ : OpenFam ℓ} (psh^𝓥 : IsPresheaf _𝓥_) where

    private open module Dummy {s} = RelLeftSemimodule (Vᴿ s)

    []ᵉ′ : ∀ {R θ} → ∀[ ℑᶜ ⇒ [ _𝓥_ ]_⇒ᵉ ctx {ε} R θ ]
    []ᵉ′ ℑ⟨ sp ⟩ .Ψ = [─]
    []ᵉ′ ℑ⟨ sp ⟩ .asLinRel = [─]AsLinRel
    []ᵉ′ ℑ⟨ sp ⟩ .sums = sp
    []ᵉ′ ℑ⟨ sp ⟩ .lookup _ (lvar (there () _) _ _)

    []ᵉ : ∀[ ℑᶜ ⇒ [ _𝓥_ ]_⇒ᵉ []ᶜ ]
    []ᵉ = []ᵉ′

    ++ᵉ′ : ∀ {s t R θ} → let Γ = ctx (R ∘ ↙) (θ ∘ ↙); Δ = ctx (R ∘ ↘) (θ ∘ ↘) in
      ∀[ [ _𝓥_ ]_⇒ᵉ Γ ✴ᶜ [ _𝓥_ ]_⇒ᵉ Δ ⇒ [ _𝓥_ ]_⇒ᵉ ctx {s <+> t} R θ ]
    ++ᵉ′ (ρ ✴⟨ sp ⟩ σ) .Ψ = [ ρ .Ψ ─ σ .Ψ ]
    ++ᵉ′ (ρ ✴⟨ sp ⟩ σ) .asLinRel = [ ρ .asLinRel ─ σ .asLinRel ]AsLinRel
    ++ᵉ′ (ρ ✴⟨ sp ⟩ σ) .sums = ρ .sums ↘, sp ,↙ σ .sums
    ++ᵉ′ (ρ ✴⟨ sp ⟩ σ) .lookup (r ↘, r+s ,↙ s) (lvar (↙ i) q b) =
      let br , bs = un++ₙ b in
      let v = ρ .lookup r (lvar i q br) in
      psh^𝓥 (+ₘ-identityʳ→ (r+s , σ .asLinRel .linRel .rel-0ₘ (≤*→0* bs , s))) v
    ++ᵉ′ (ρ ✴⟨ sp ⟩ σ) .lookup (r ↘, r+s ,↙ s) (lvar (↘ i) q b) =
      let br , bs = un++ₙ b in
      let v = σ .lookup s (lvar i q bs) in
      psh^𝓥 (+ₘ-identityˡ→ (ρ .asLinRel .linRel .rel-0ₘ (≤*→0* br , r) , r+s)) v

    ++ᵉ : ∀[ [ _𝓥_ ]_⇒ᵉ Γ ✴ᶜ [ _𝓥_ ]_⇒ᵉ Δ ⇒ [ _𝓥_ ]_⇒ᵉ Γ ++ᶜ Δ ]
    ++ᵉ = ++ᵉ′

    [-]ᵉ′ : ∀ {R θ} → ∀[ R here ·ᶜ _𝓥 θ here Syn.⇒ [ _𝓥_ ]_⇒ᵉ ctx {[-]} R θ ]
    [-]ᵉ′ (⟨_⟩·_ {Q′} sp v) .Ψ = [─ Q′ ─]
    [-]ᵉ′ (⟨_⟩·_ {Q′} sp v) .asLinRel = [─ Q′ ─]AsLinRel
    [-]ᵉ′ (⟨ sp ⟩· v) .sums = sp
    [-]ᵉ′ (⟨ sp ⟩· v) .lookup t (lvar here refl b) =
      psh^𝓥 (*ₘ-identity→ (b .get here , t)) v

    [-]ᵉ : ∀ {r A} → ∀[ r ·ᶜ _𝓥 A Syn.⇒ [ _𝓥_ ]_⇒ᵉ [ r · A ]ᶜ ]
    [-]ᵉ = [-]ᵉ′
