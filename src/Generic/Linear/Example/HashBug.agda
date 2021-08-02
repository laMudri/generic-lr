{-# OPTIONS --sized-types --without-K --postfix-projections --prop #-}

module Generic.Linear.Example.HashBug where

  open import Algebra.Po
  open import Data.LTree
  open import Data.LTree.Automation
  open import Data.LTree.Vector
  open import Data.Product
  open import Data.Unit using (⊤; tt)
  open import Level
  open import Proposition
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
  open import Size

  0-poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ
  0-poSemiring = record { Carrier = ⊤; _≈_ = λ _ _ → ⊤; _≤_ = λ _ _ → ⊤ }

  0-rawPoSemiring : RawPoSemiring 0ℓ 0ℓ 0ℓ
  0-rawPoSemiring = PoSemiring.rawPoSemiring 0-poSemiring

  data Ty : Set where ι : Ty

  open import Generic.Linear.Syntax Ty ⊤

  data Lbl : Set where
    `lam `app : Lbl

  flags : PremisesFlags
  flags = record noPremisesFlags { Has-∧ = ⊤ᴾ }

  Desc : System flags
  Desc = Lbl ▹ λ where
    `lam → ⟨ [ _ · ι ]ᶜ `⊢ ι ⟩ =⇒ ι
    `app → ⟨ []ᶜ `⊢ ι ⟩ `∧ ⟨ []ᶜ `⊢ ι ⟩ =⇒ ι

  open import Generic.Linear.Syntax.Term Ty 0-rawPoSemiring
  open import Generic.Linear.Variable Ty 0-rawPoSemiring

  pattern var i = `var (lvar i ≡.refl _)
  pattern lam M = `con (`lam , ≡.refl , M)
  pattern app M N = `con (`app , ≡.refl , M , N)

  import Function.Base as F

  test₀ test₁ test₂ test₃ test₄ : [ Desc , ∞ ] []ᶜ ⊢ ι
  test₀ = lam (lam (app (var (# 1)) (var (# 0))))
  -- Yellow:   ^-------------------------------^
  test₁ = lam (lam (app (var (Ptr (((ε <+> [-]) <+> [-]) <+> ε) F.∋ # 1)) (var (# 0))))
  -- By C-u C-u C-c C-s:      ^-------------------------------^
  test₂ = lam (lam (app (var (_ F.∋ # 1)) (var (# 0))))
  -- Yellow:   ^-------------------------------------^
  test₃ = lam (lam (app (`var (lvar (# 1) {!!} _)) (var (# 0))))
  -- No yellow.                           ^ Normalised goal: ι ≡ ι
  -- C-c C-x C-h C-c C-, shows that all implicit arguments to # 1 have been
  --   solved.
  test₄ = lam (lam (var (# 1)))
  -- This is fine.
