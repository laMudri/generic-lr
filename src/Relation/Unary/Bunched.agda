{-# OPTIONS --safe --without-K #-}

module Relation.Unary.Bunched where

  open import Data.Bool.Base
  open import Data.Bool.Extra
  open import Data.Product
  open import Data.Unit.Polymorphic using (⊤; tt)
  open import Level
  open import Relation.Unary

  module BunchedOrder {a ℓ} {A : Set a} (_≤_ : A → A → Set ℓ) where

    infixr 8 _⇒ᵏ_

    _⇒ᵏ_ : ∀ {t u} (T : A → Set t) (U : A → Set u) → A → Set (a ⊔ ℓ ⊔ t ⊔ u)
    (T ⇒ᵏ U) x = ∀ {y} → y ≤ x → T y → U y

    record ◇ {t} (T : A → Set t) (x : A) : Set (a ⊔ ℓ ⊔ t) where
      constructor ◇⟨_⟩_
      field
        {y} : A
        sub : x ≤ y
        T-prf : T y

  open BunchedOrder public using (◇⟨_⟩_)

  module BunchedUnit {a ℓ} {A : Set a} (_∼0 : A → Set ℓ) where

    record ℑ {v} (x : A) : Set (ℓ ⊔ v) where
      constructor ℑ⟨_⟩
      field
        split : x ∼0

  open BunchedUnit public using (ℑ⟨_⟩)

  module BunchedConjunction {a ℓ} {A : Set a} (_∼_+_ : A → A → A → Set ℓ) where

    infixr 8 _─✴_
    infixr 9 _✴_ _✴⟨_⟩_

    record _✴_ {t u} (T : A → Set t) (U : A → Set u) (x : A)
               : Set (a ⊔ ℓ ⊔ t ⊔ u) where
      constructor _✴⟨_⟩_
      field
        {y z} : A
        T-prf : T y
        split : x ∼ y + z
        U-prf : U z

    record _─✴_ {t u} (T : A → Set t) (U : A → Set u) (x : A)
                : Set (a ⊔ ℓ ⊔ t ⊔ u) where
      constructor lam✴
      field
        app✴ : ∀ {y z} (split : z ∼ x + y) (T-prf : T y) → U z
    open _─✴_ public

    map-✴ : ∀ {t t′ u u′} {T : A → Set t} {T′ : A → Set t′}
                          {U : A → Set u} {U′ : A → Set u′} →
            T ⊆ T′ × U ⊆ U′ → T ✴ U ⊆ T′ ✴ U′
    map-✴ (f , g) (t ✴⟨ sp ⟩ u) = f t ✴⟨ sp ⟩ g u

  open BunchedConjunction public using (_✴⟨_⟩_; lam✴; app✴)

  module BunchedScaling {a r ℓ} {A : Set a} {R : Set r}
    (_∼_*ₗ_ : A → R → A → Set ℓ)
    where

    infixr 10 _·_ ⟨_⟩·_

    record _·_ {t} (r : R) (T : A → Set t) (x : A) : Set (a ⊔ ℓ ⊔ t) where
      constructor ⟨_⟩·_
      field
        {z} : A
        split : x ∼ r *ₗ z
        T-prf : T z

    map-· : ∀ {r t t′} {T : A → Set t} {T′ : A → Set t′} →
      T ⊆ T′ → r · T ⊆ r · T′
    map-· f (⟨ sp ⟩· t) = ⟨ sp ⟩· f t

  open BunchedScaling public using (⟨_⟩·_)

  record BoxFlags : Set where
    constructor boxFlags
    field p0 p+ p* : Bool

  module BunchedDuplicable
    {a r ℓ} {A : Set a} {R : Set r} (_≤_ : A → A → Set ℓ)
    (_∼0 : A → Set ℓ) (_∼_+_ : A → A → A → Set ℓ) (_∼_*ₗ_ : A → R → A → Set ℓ)
    where

    infixr 10 □⟨_,_,_,_⟩_

    record Dup (bf : BoxFlags) {t} (T : A → Set t) (x : A)
           : Set (a ⊔ r ⊔ ℓ ⊔ t) where
      constructor □⟨_,_,_,_⟩_
      open BoxFlags bf
      field
        {y} : _
        strengthen : x ≤ y
        split-0 : If p0 (y ∼0)
        split-+ : If p+ (y ∼ y + y)
        split-* : If p* (∀ r → y ∼ r *ₗ y)
        T-prf : T y

  open BunchedDuplicable public using (□⟨_,_,_,_⟩_)

  module BunchedModal {a ℓ} {A : Set a} (R : A → A → Set ℓ) where

    infixr 10 □⟨_⟩_

    record Box {t} (T : A → Set t) (x : A) : Set (a ⊔ ℓ ⊔ t) where
      constructor □⟨_⟩_
      field
        {y} : _
        R-prf : R x y
        T-prf : T y

  open BunchedModal public using (□⟨_⟩_)

  module Duplicable
    {A R : Set} (_≤_ : A → A → Set)
    (_≤0 : A → Set) (_≤[_+_] : A → A → A → Set) (_≤[_*ₗ_] : A → R → A → Set)
    where

    record Dup (P Q : A) : Set where
      constructor mkDup
      field
        strengthen : P ≤ Q
        split-0 : Q ≤0
        split-+ : Q ≤[ Q + Q ]
        split-* : ∀ r → Q ≤[ r *ₗ Q ]

  open Duplicable public using (mkDup)
