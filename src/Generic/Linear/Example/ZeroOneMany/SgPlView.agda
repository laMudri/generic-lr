{-# OPTIONS --sized-types --without-K --postfix-projections #-}

module Generic.Linear.Example.ZeroOneMany.SgPlView where

  open import Generic.Linear.Example.ZeroOneMany renaming (u01ω to Ann)

  open import Data.Bool using (Bool; true; false; if_then_else_)
  open import Data.Product
  open import Function.Base using (case_of_)
  open import Relation.Binary.PropositionalEquality

  data Plural : Ann → Set where
    u0-plural : Plural u0
    uω-plural : Plural uω

  ω*-plural : ∀ x → Plural (uω * x)
  ω*-plural u0 = u0-plural
  ω*-plural u1 = uω-plural
  ω*-plural uω = uω-plural

  data SPView : Ann → Set where
    view-sg : SPView u1
    view-pl : ∀ {x} (p : Plural x) → SPView x

  spview : ∀ x → SPView x
  spview u0 = view-pl u0-plural
  spview u1 = view-sg
  spview uω = view-pl uω-plural

  spview-prop : ∀ {x} (u v : SPView x) → u ≡ v
  spview-prop view-sg view-sg = refl
  spview-prop (view-pl u0-plural) (view-pl u0-plural) = refl
  spview-prop (view-pl uω-plural) (view-pl uω-plural) = refl

  is-plural : Ann → Bool
  is-plural x = case spview x of λ where
    view-sg → false
    (view-pl _) → true
