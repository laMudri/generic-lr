{-# OPTIONS --safe --without-K #-}

module Generic.Linear.Syntax.Core where

  open import Data.Bool

  record PremisesFlags : Set where
    field
      ⊤? ∧? ℑ? ✴? ·? □? : Bool

    Has-⊤ Has-∧ Has-ℑ Has-✴ Has-· Has-□ : Set
    Has-⊤ = T ⊤?
    Has-∧ = T ∧?
    Has-ℑ = T ℑ?
    Has-✴ = T ✴?
    Has-· = T ·?
    Has-□ = T □?

  noPremisesFlags : PremisesFlags
  noPremisesFlags = record
    { ⊤? = false ; ∧? = false ; ℑ? = false ; ✴? = false
    ; ·? = false ; □? = false
    }

  allPremisesFlags : PremisesFlags
  allPremisesFlags = record
    { ⊤? = true ; ∧? = true ; ℑ? = true ; ✴? = true
    ; ·? = true ; □? = true
    }
