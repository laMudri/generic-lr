{-# OPTIONS --safe --without-K --prop #-}

module Generic.Linear.Syntax.Core where

  open import Proposition

  record PremisesFlags : Set₁ where
    field
      Has-⊤ Has-∧ Has-ℑ Has-✴ Has-· Has-□ : Prop

  noPremisesFlags : PremisesFlags
  noPremisesFlags = record
    { Has-⊤ = ⊥ᴾ; Has-∧ = ⊥ᴾ; Has-ℑ = ⊥ᴾ; Has-✴ = ⊥ᴾ; Has-· = ⊥ᴾ; Has-□ = ⊥ᴾ }

  allPremisesFlags : PremisesFlags
  allPremisesFlags = record
    { Has-⊤ = ⊤ᴾ; Has-∧ = ⊤ᴾ; Has-ℑ = ⊤ᴾ; Has-✴ = ⊤ᴾ; Has-· = ⊤ᴾ; Has-□ = ⊤ᴾ }
