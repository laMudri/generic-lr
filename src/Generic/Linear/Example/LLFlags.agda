{-# OPTIONS --safe --without-K --prop --postfix-projections #-}

module Generic.Linear.Example.LLFlags where

  open import Proposition

  record LLFlags : Set₁ where
    field
      Has-0 Has-⊕ Has-⊤ Has-& Has-I Has-⊗ Has-⊸ Has-! Has-ℕ : Prop

  noLLFlags : LLFlags
  noLLFlags = record
    { Has-0 = ⊥ᴾ; Has-⊕ = ⊥ᴾ; Has-⊤ = ⊥ᴾ; Has-& = ⊥ᴾ
    ; Has-I = ⊥ᴾ; Has-⊗ = ⊥ᴾ; Has-⊸ = ⊥ᴾ; Has-! = ⊥ᴾ; Has-ℕ = ⊥ᴾ
    }

  allLLFlags : LLFlags
  allLLFlags = record
    { Has-0 = ⊤ᴾ; Has-⊕ = ⊤ᴾ; Has-⊤ = ⊤ᴾ; Has-& = ⊤ᴾ
    ; Has-I = ⊤ᴾ; Has-⊗ = ⊤ᴾ; Has-⊸ = ⊤ᴾ; Has-! = ⊤ᴾ; Has-ℕ = ⊤ᴾ
    }
