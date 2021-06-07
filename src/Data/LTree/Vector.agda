{-# OPTIONS --safe --without-K --postfix-projections #-}

-- Functional vectors indexed by tree sizes

module Data.LTree.Vector where

  open import Data.LTree

  open import Algebra.Core using (Op₂)
  open import Data.Product using (_×_; _,_; uncurry)
  open import Data.Product.Relation.Binary.Pointwise.NonDependent as ×PW
    using (×-setoid)
  open import Data.Unit using (⊤; tt)
  open import Function.Base using (id; _∘_)
  open import Function.Equality using (_⟶_; _⟨$⟩_; cong)
  open import Level using (Level; _⊔_; 0ℓ)
  open import Relation.Binary
    using (REL; Rel; Setoid; IsEquivalence; Reflexive)
  open import Relation.Binary.Construct.Always as ⊤ using ()
  open import Relation.Unary using (Pred)

  private
    variable
      a b c r ℓ : Level
      A : Set a
      B : Set b
      C : Set c
      s t : LTree

  infix 5 _++_

  Vector : Set a → LTree → Set a
  Vector A s = Ptr s → A

  lift₀ : A → ∀ {s} → Vector A s
  lift₀ x _ = x

  lift₁ : (A → B) → ∀ {s} → Vector A s → Vector B s
  lift₁ f u i = f (u i)

  lift₂ : (A → B → C) → ∀ {s} → Vector A s → Vector B s → Vector C s
  lift₂ f u v i = f (u i) (v i)

  record Lift₁ (R : Pred A r) {s} (u : Vector A s) : Set r where
    constructor mk
    field get : ∀ i → R (u i)
  open Lift₁ public

  record Lift₂ (R : REL A B r) {s} (u : Vector A s) (v : Vector B s)
               : Set r where
    constructor mk
    field get : ∀ i → R (u i) (v i)
  open Lift₂ public

  [_] : A → Vector A [-]
  [ x ] _ = x

  [] : Vector A ε
  [] (there () _)

  _++_ : Vector A s → Vector A t → Vector A (s <+> t)
  (u ++ v) (↙ i) = u i
  (u ++ v) (↘ j) = v j

  un[-] : Vector A [-] → A
  un[-] v = v here

  un++ : Vector A (s <+> t) → Vector A s × Vector A t
  un++ v = v ∘ there left , v ∘ there right

  module _ {R : Pred A r} where

    infix 5 _++₁_

    [_]₁ : {u : Vector A [-]} → R (u here) → Lift₁ R u
    [ r ]₁ .get here = r

    []₁ : {u : Vector A ε} → Lift₁ R u
    []₁ .get (there () _)

    _++₁_ : {u : Vector A (s <+> t)} →
            Lift₁ R (u ∘ ↙) → Lift₁ R (u ∘ ↘) → Lift₁ R u
    (ru ++₁ rv) .get (↙ i) = ru .get i
    (ru ++₁ rv) .get (↘ i) = rv .get i

  module _ {R : REL A B r} where

    infix 5 _++₂_

    [_]₂ : {u : Vector A [-]} {v : Vector B [-]} →
           R (u here) (v here) → Lift₂ R u v
    [ r ]₂ .get here = r

    []₂ : {u : Vector A ε} {v : Vector B ε} → Lift₂ R u v
    []₂ .get (there () _)

    _++₂_ : {u : Vector A (s <+> t)} {v : Vector B (s <+> t)} →
      Lift₂ R (u ∘ ↙) (v ∘ ↙) → Lift₂ R (u ∘ ↘) (v ∘ ↘) → Lift₂ R u v
    (ru ++₂ rv) .get (↙ i) = ru .get i
    (ru ++₂ rv) .get (↘ i) = rv .get i

    un[-]₂ : {u : Vector A [-]} {v : Vector B [-]} →
             Lift₂ R u v → R (u here) (v here)
    un[-]₂ r = r .get here

    un++₂ : {u : Vector A (s <+> t)} {v : Vector B (s <+> t)} →
            Lift₂ R u v →
            Lift₂ R (u ∘ ↙) (v ∘ ↙) × Lift₂ R (u ∘ ↘) (v ∘ ↘)
    un++₂ (mk r) = mk (r ∘ ↙) , mk (r ∘ ↘)

  module _ (b : A → B) (e : B) (a : B → B → B) where

    fold : Vector A s → B
    fold {[-]} u = b (u here)
    fold {ε} u = e
    fold {s <+> t} u = a (fold (u ∘ ↙)) (fold (u ∘ ↘))

  module Sum (0# : A) (_+_ : Op₂ A) where
    ∑ = fold id 0# _+_

  module _ where
    open Setoid
    open IsEquivalence

    setoid : Setoid a ℓ → LTree → Setoid a ℓ
    setoid S s .Carrier = Vector (S .Carrier) s
    setoid S s ._≈_ = Lift₂ (S ._≈_)
    setoid S s .isEquivalence .refl .get i = S .refl
    setoid S s .isEquivalence .sym p .get i = S .sym (p .get i)
    setoid S s .isEquivalence .trans p q .get i =
      S .trans (p .get i) (q .get i)

    [-]ˢ : ∀ {S} → S ⟶ setoid {a} {ℓ} S [-]
    [-]ˢ ._⟨$⟩_ = [_]
    [-]ˢ .cong = [_]₂

    []ˢ : ∀ {S} → ⊤.setoid ⊤ 0ℓ ⟶ setoid {a} {ℓ} S ε
    []ˢ ⟨$⟩ _ = []
    []ˢ .cong _ = []₂

    ++ˢ : ∀ {S} →
          ×-setoid (setoid S s) (setoid S t) ⟶ setoid {a} {ℓ} S (s <+> t)
    ++ˢ ⟨$⟩ (xs , ys) = xs ++ ys
    ++ˢ .cong (p , q) = p ++₂ q

    infix 5 _++₁∼_

    record Lift₁∼ {R : Pred A r} (_∼_ : ∀ {x} → Rel (R x) ℓ)
                  {s} {xs : Vector A s} (ρ σ : Lift₁ R xs) : Set ℓ where
      constructor mk
      field get : ∀ i → ρ .get i ∼ σ .get i
    open Lift₁∼ public

    setoidL₁ : (A → Setoid r ℓ) → (Vector A s → Setoid r ℓ)
    setoidL₁ S xs .Carrier = Lift₁ (Carrier ∘ S) xs
    setoidL₁ S xs ._≈_ ρ σ = Lift₁∼ (S _ ._≈_) ρ σ
    setoidL₁ S xs .isEquivalence .refl .get i = S _ .refl
    setoidL₁ S xs .isEquivalence .sym p .get i = S _ .sym (p .get i)
    setoidL₁ S xs .isEquivalence .trans p q .get i =
      S _ .trans (p .get i) (q .get i)

    [_]₁∼ : ∀ {R : Pred A r} {_∼_ : ∀ {x} → Rel (R x) ℓ} {xs a b} →
            a ∼ b → Lift₁∼ {R = R} _∼_ {xs = xs} [ a ]₁ [ b ]₁
    [ p ]₁∼ .get here = p

    []₁∼ : ∀ {R : Pred A r} {∼ : ∀ {x} → Rel (R x) ℓ} {xs} →
           Lift₁∼ {R = R} ∼ {xs = xs} []₁ []₁
    []₁∼ .get (there () i)

    _++₁∼_ : ∀ {R : Pred A r} {∼ : ∀ {x} → Rel (R x) ℓ} {s t xs ρl ρr σl σr} →
             Lift₁∼ ∼ {s} {xs ∘ ↙} ρl σl →
             Lift₁∼ ∼ {t} {xs ∘ ↘} ρr σr →
             Lift₁∼ {R = R} ∼ {xs = xs} (ρl ++₁ ρr) (σl ++₁ σr)
    (pl ++₁∼ pr) .get (↙ i) = pl .get i
    (pl ++₁∼ pr) .get (↘ i) = pr .get i

    [-]₁ˢ : ∀ {S xs} → S (xs here) ⟶ setoidL₁ {A = A} {r} {ℓ} S xs
    [-]₁ˢ ._⟨$⟩_ = [_]₁
    [-]₁ˢ .cong = [_]₁∼

    []₁ˢ : ∀ {S xs} → ⊤.setoid ⊤ 0ℓ ⟶ setoidL₁ {A = A} {r} {ℓ} {ε} S xs
    []₁ˢ ⟨$⟩ _ = []₁
    []₁ˢ .cong _ = []₁∼

    ++₁ˢ :
      ∀ {S xs} →
      ×-setoid (setoidL₁ {s = s} S (xs ∘ ↙)) (setoidL₁ {s = t} S (xs ∘ ↘)) ⟶
      setoidL₁ {A = A} {r} {ℓ} S xs
    ++₁ˢ ._⟨$⟩_ = uncurry _++₁_
    ++₁ˢ .cong = uncurry _++₁∼_

    []₁η : ∀ {R : Pred A r} {∼ : ∀ {x} → Rel (R x) ℓ}
           (refl : ∀ {x} → Reflexive (∼ {x})) {xs ρ} →
           Lift₁∼ {R = R} ∼ {ε} {xs} []₁ ρ
    []₁η refl .get (there () i)

    [-]₁η : ∀ {R : Pred A r} {∼ : ∀ {x} → Rel (R x) ℓ}
            (refl : ∀ {x} → Reflexive (∼ {x})) {xs ρ} →
            Lift₁∼ {R = R} ∼ {[-]} {xs} [ ρ .get here ]₁ ρ
    [-]₁η refl .get here = refl

    ++₁η :
      ∀ {R : Pred A r} {∼ : ∀ {x} → Rel (R x) ℓ}
      (refl : ∀ {x} → Reflexive (∼ {x})) {xs ρ} →
      Lift₁∼ {R = R} ∼ {s <+> t} {xs} (mk (ρ .get ∘ ↙) ++₁ mk (ρ .get ∘ ↘)) ρ
    ++₁η refl .get (↙ i) = refl
    ++₁η refl .get (↘ i) = refl
