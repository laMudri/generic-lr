{-# OPTIONS --safe --without-K #-}

open import Algebra.Core
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel)

module Generic.Linear.Semantics
  (Ty Ann : Set) (_⊴_ : Rel Ann 0ℓ)
  (0# : Ann) (_+_ : Op₂ Ann) (1# : Ann) (_*_ : Op₂ Ann)
  where

  open import Relation.Unary

  open import Generic.Linear.Syntax Ty Ann
  import Generic.Linear.Syntax.Term Ty Ann _⊴_ 0# _+_ 1# _*_ as Term
  open import Generic.Linear.Environment Ty Ann _⊴_ 0# _+_ 1# _*_ hiding (var)
  open import Generic.Linear.Thinning Ty Ann _⊴_ 0# _+_ 1# _*_

  private
    variable
      A : Ty

  record Semantics (d : System) (𝓥 𝓒 : Scoped) : Set where
    open Term (λ PΓ A → □ ((PΓ ─Env) 𝓥 ⇒ 𝓒 A))
    field
      th^𝓥 : Thinnable (𝓥 A)
      var : ∀[ 𝓥 A ⇒ 𝓒 A ]
      alg : ∀[ ⟦ d ⟧s A ⇒ 𝓒 A ]
