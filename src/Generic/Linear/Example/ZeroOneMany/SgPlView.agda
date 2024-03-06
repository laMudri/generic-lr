{-# OPTIONS --sized-types --without-K --postfix-projections #-}

module Generic.Linear.Example.ZeroOneMany.SgPlView where

  open import Generic.Linear.Example.ZeroOneMany renaming (0#1ω to Ann)

  open import Data.Bool using (Bool; true; false; if_then_else_)
  open import Data.Product
  open import Function.Base using (case_of_)
  open import Relation.Binary.PropositionalEquality

  data Plural : Ann → Set where
    0#-plural : Plural 0#
    ω#-plural : Plural ω#

  ω*-plural : ∀ x → Plural (ω# * x)
  ω*-plural 0# = 0#-plural
  ω*-plural 1# = ω#-plural
  ω*-plural ω# = ω#-plural

  data SPView : Ann → Set where
    view-sg : SPView 1#
    view-pl : ∀ {x} (p : Plural x) → SPView x

  spview : ∀ x → SPView x
  spview 0# = view-pl 0#-plural
  spview 1# = view-sg
  spview ω# = view-pl ω#-plural

  spview-prop : ∀ {x} (u v : SPView x) → u ≡ v
  spview-prop view-sg view-sg = refl
  spview-prop (view-pl 0#-plural) (view-pl 0#-plural) = refl
  spview-prop (view-pl ω#-plural) (view-pl ω#-plural) = refl

  is-plural : Ann → Bool
  is-plural x = case spview x of λ where
    view-sg → false
    (view-pl _) → true
