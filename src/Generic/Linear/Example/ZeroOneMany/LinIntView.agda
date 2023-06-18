{-# OPTIONS --sized-types --without-K --postfix-projections #-}

module Generic.Linear.Example.ZeroOneMany.LinIntView where

  open import Generic.Linear.Example.ZeroOneMany renaming (u01ω to Ann)

  open import Data.Bool using (Bool; true; false; if_then_else_)
  open import Data.Product
  open import Function.Base using (case_of_)
  open import Relation.Binary.PropositionalEquality

  data Linear : Ann → Set where
    u0-lin : Linear u0
    u1-lin : Linear u1

  linear-≤ : ∀ {x y} → x ≤ y → Linear x → Linear y
  linear-≤ ≤-refl l = l

  linear-summands : ∀ {z x y} → z ≤ x + y → Linear z → Linear x × Linear y
  linear-summands {u0} {u0} {.u0} ≤-refl u0-lin = u0-lin , u0-lin
  linear-summands {u0} {u1} {u0} () u0-lin
  linear-summands {u0} {u1} {u1} () u0-lin
  linear-summands {u0} {u1} {uω} () u0-lin
  linear-summands {u1} {u0} {.u1} ≤-refl u1-lin = u0-lin , u1-lin
  linear-summands {u1} {u1} {u0} le u1-lin = u1-lin , u0-lin

  linear-/ω : ∀ {z y} → z ≤ uω * y → Linear z → Linear y
  linear-/ω {z} {u0} le l = u0-lin
  linear-/ω {z} {u1} le l = u1-lin
  linear-/ω {.(uω * uω)} {uω} ≤-refl ()

  data LIView : Ann → Set where
    view-lin : ∀ {x} (l : Linear x) → LIView x
    view-int : LIView uω

  liview : ∀ x → LIView x
  liview u0 = view-lin u0-lin
  liview u1 = view-lin u1-lin
  liview uω = view-int

  liview-prop : ∀ {x} (u v : LIView x) → u ≡ v
  liview-prop view-int view-int = refl
  liview-prop (view-lin u0-lin) (view-lin u0-lin) = refl
  liview-prop (view-lin u1-lin) (view-lin u1-lin) = refl

  is-lin : Ann → Bool
  is-lin x = case liview x of λ where
    view-int → false
    (view-lin _) → true
