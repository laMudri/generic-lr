{-# OPTIONS --safe --without-K --postfix-projections #-}

-- Functional vectors indexed by tree sizes

module Data.LTree.Vector where

  open import Data.LTree

  open import Algebra.Core using (Op₂)
  open import Data.Product using (_×_; proj₁; proj₂; _,_; uncurry)
  open import Data.Product.Relation.Binary.Pointwise.NonDependent as ×PW
    using (×-setoid)
  open import Data.Product.Nary.NonDependent
  open import Data.Unit using (⊤; tt)
  open import Function.Base using (id; _∘_; _$_; case_of_; case_return_of_; _∋_)
  open import Function.Equality using (_⟶_; _⟨$⟩_; cong)
  open import Function.Nary.NonDependent
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

  open import Data.Nat.Base using (ℕ; zero; suc)
  open import Data.Fin.Base using (Fin; zero; suc)
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_)

  -- TODO: contribute Product⊤ₙ stuff to stdlib

  {-
  tabulate⊤ₙ : ∀ n {ls} {as : Sets n ls} → (∀ k → Projₙ as k) → Product⊤ n as
  tabulate⊤ₙ zero f = _
  tabulate⊤ₙ (suc n) f = f zero , tabulate⊤ₙ n λ k → f (suc k)

  proj⊤ₙ : ∀ n {ls} {as : Sets n ls} k → Product⊤ n as → Projₙ as k
  proj⊤ₙ _ zero (x , xs) = x
  proj⊤ₙ _ (suc k) (x , xs) = proj⊤ₙ _ k xs
  -}

  map×⊤ₙ :
    ∀ {f g} {F : ∀ {l} → Set l → Set (f l)} {G : ∀ {l} → Set l → Set (g l)} →
    (∀ {a} {A : Set a} → F A → G A) →
    ∀ n {as} {As : Sets n as} →
    (Product⊤ n (smap f F n As) → Product⊤ n (smap g G n As))
  map×⊤ₙ h zero tt = tt
  map×⊤ₙ h (suc n) (x , xs) = h x , map×⊤ₙ h n xs

  map×⊤ₙ← : ∀ {f} {F : ∀ {l} → Set l → Set (f l)} →
    (∀ {a} {A : Set a} → F A → A) →
    ∀ n {as} {As : Sets n as} → (Product⊤ n (smap f F n As) → Product⊤ n As)
  map×⊤ₙ← g zero tt = tt
  map×⊤ₙ← g (suc n) (x , xs) = g x , map×⊤ₙ← g n xs

  map×⊤ₙ→ : ∀ {f} {F : ∀ {l} → Set l → Set (f l)} →
    (∀ {a} {A : Set a} → A → F A) →
    ∀ n {as} {As : Sets n as} → (Product⊤ n As → Product⊤ n (smap f F n As))
  map×⊤ₙ→ g zero tt = tt
  map×⊤ₙ→ g (suc n) (x , xs) = g x , map×⊤ₙ→ g n xs

  map×⊤ₙ←∘map×⊤ₙ-→ : ∀ n {as} {As : Sets n as} {f g : Level → Level}
    {F : ∀ {l} → Set l → Set (f l)} {G : ∀ {l} → Set l → Set (g l)}
    {p} (P : Product⊤ n As → Set p)
    (i : ∀ {a} {A : Set a} → F A → A) (j : ∀ {a} {A : Set a} → G A → F A)
    (xs : Product⊤ n (smap g G n As)) →
    P (map×⊤ₙ← i n (map×⊤ₙ j n xs)) → P (map×⊤ₙ← (i ∘ j) n xs)
  map×⊤ₙ←∘map×⊤ₙ-→ zero P i j tt p = p
  map×⊤ₙ←∘map×⊤ₙ-→ (suc n) P i j (x , xs) p =
    map×⊤ₙ←∘map×⊤ₙ-→ n (λ xs → P (i (j x) , xs)) i j xs p

  map×⊤ₙ←∘map×⊤ₙ-← : ∀ n {as} {As : Sets n as} {f g : Level → Level}
    {F : ∀ {l} → Set l → Set (f l)} {G : ∀ {l} → Set l → Set (g l)}
    {p} (P : Product⊤ n As → Set p)
    {i : ∀ {a} {A : Set a} → F A → A} {j : ∀ {a} {A : Set a} → G A → F A}
    {xs : Product⊤ n (smap g G n As)} →
    P (map×⊤ₙ← (i ∘ j) n xs) → P (map×⊤ₙ← i n (map×⊤ₙ j n xs))
  map×⊤ₙ←∘map×⊤ₙ-← zero P {xs = tt} p = p
  map×⊤ₙ←∘map×⊤ₙ-← (suc n) P {i} {j} {xs = x , xs} p =
    map×⊤ₙ←∘map×⊤ₙ-← n (λ xs → P (i (j x) , xs)) {xs = xs} p

  const×⊤ₙ :
    ∀ {f} {F : ∀ {a} → Set a → Set (f a)} → (∀ {a} {A : Set a} → F A) →
    ∀ {n as} {As : Sets n as} → Product⊤ n (smap f F n As)
  const×⊤ₙ x {zero} = tt
  const×⊤ₙ x {suc n} = x , const×⊤ₙ x {n}

  zipWith×⊤ₙ :
    ∀ {f g h} {F : ∀ {l} → Set l → Set (f l)} {G : ∀ {l} → Set l → Set (g l)}
    {H : ∀ {l} → Set l → Set (h l)} → (∀ {a} {A : Set a} → F A → G A → H A) →
    ∀ {n as} {As : Sets n as} →
    Product⊤ n (smap f F n As) → Product⊤ n (smap g G n As) →
    Product⊤ n (smap h H n As)
  zipWith×⊤ₙ c {zero} tt tt = tt
  zipWith×⊤ₙ c {suc n} (x , xs) (y , ys) = c x y , zipWith×⊤ₙ c {n} xs ys

  -- map×⊤ₙ←∘zipWith×⊤ₙ-← : ∀ n {as} {As : Sets n as} {f g h : Level → Level}
  --   {F : ∀ {l} → Set l → Set (f l)} {G : ∀ {l} → Set l → Set (g l)}
  --   {H : ∀ {l} → Set l → Set (h l)}
  --   {p} (P : Product⊤ n As → Set p)
  --   (i : ∀ {a} {A : Set a} → F A → A) (j : ∀ {a} {A : Set a} → G A → H A → F A)
  --   (xs : Product⊤ n (smap g G n As)) (ys : Product⊤ n (smap h H n As)) →
  --   P (zipWith×⊤ₙ (λ x y → i (j x y)) xs ys) → P (map×⊤ₙ← i n (zipWith×⊤ₙ j xs ys))
  -- map×⊤ₙ←∘zipWith×⊤ₙ-← n P i j xs p = ?
  -- map×⊤ₙ←∘map×⊤ₙ-← zero P i j tt p = p
  -- map×⊤ₙ←∘map×⊤ₙ-← (suc n) P i j (x , xs) p =
  --   map×⊤ₙ←∘map×⊤ₙ-← n (λ xs → P (i (j x) , xs)) i j xs p

  record Liftₙ′ {n as r} {As : Sets n as} (R : As ⇉ Set r)
    {s} (vs : Product⊤ n (smap id (λ A → Vector A s) n As)) : Set r where
    constructor mk
    field get : ∀ (i : Ptr s) → uncurry⊤ₙ n R (map×⊤ₙ← (_$ i) n vs)
  open Liftₙ′ public

  Liftₙ : ∀ {n as r} {As : Sets n as} (R : As ⇉ Set r) {s} →
    smap id (λ A → Vector A s) n As ⇉ Set r
  Liftₙ {n} R = curry⊤ₙ n (Liftₙ′ R)

  [_] : A → Vector A [-]
  [ x ] _ = x

  [] : Vector A ε
  [] ()

  _++_ : Vector A s → Vector A t → Vector A (s <+> t)
  (u ++ v) (↙ i) = u i
  (u ++ v) (↘ j) = v j

  un[-] : Vector A [-] → A
  un[-] v = v here

  un++ : Vector A (s <+> t) → Vector A s × Vector A t
  un++ v = v ∘ ↙ , v ∘ ↘

  module _ {R : Pred A r} where

    infix 5 _++₁_

    [_]₁ : {u : Vector A [-]} → R (u here) → Lift₁ R u
    [ r ]₁ .get here = r

    []₁ : {u : Vector A ε} → Lift₁ R u
    []₁ .get ()

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
    []₂ .get ()

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

  module _ {n as r} {As : Sets n as} {R : As ⇉ Set r} where

    infix 5 _++ₙ_ _++ₙ⁺_

    [_]ₙ : {vs : Product⊤ n (smap id (λ A → Vector A [-]) n As)} →
      uncurry⊤ₙ n R (map×⊤ₙ← (_$ here) n vs) → Liftₙ′ R vs
    [ r ]ₙ .get here = r

    []ₙ : {vs : Product⊤ n (smap id (λ A → Vector A ε) n As)} → Liftₙ′ R vs
    []ₙ .get ()

    _++ₙ_ :
      ∀ {s t} {vs : Product⊤ n (smap id (λ A → Vector A (s <+> t)) n As)} →
      Liftₙ′ R (map×⊤ₙ (_∘ ↙) n vs) → Liftₙ′ R (map×⊤ₙ (_∘ ↘) n vs) →
      Liftₙ′ R vs
    (ru ++ₙ rv) .get (↙ i) =
      map×⊤ₙ←∘map×⊤ₙ-→ n (uncurry⊤ₙ n R) _ _ _ (ru .get i)
    (ru ++ₙ rv) .get (↘ i) =
      map×⊤ₙ←∘map×⊤ₙ-→ n (uncurry⊤ₙ n R) _ _ _ (rv .get i)

    -- The ⁺-variants synthesise the shape of the vectors they relate.

    [_]ₙ⁺ : {xs : Product⊤ n As} →
      uncurry⊤ₙ n R xs → Liftₙ′ R (map×⊤ₙ→ [_] n xs)
    [ rx ]ₙ⁺ = [ lemma R rx ]ₙ
      where
      lemma : ∀ {n as} {As : Sets n as} (R : As ⇉ Set r) {xs : Product⊤ n As} →
        uncurry⊤ₙ n R xs →
        uncurry⊤ₙ n R (map×⊤ₙ← (_$ here) n (map×⊤ₙ→ [_] n xs))
      lemma {zero} R r = r
      lemma {suc n} R r = lemma {n} (R _) r

    []ₙ⁺ : Liftₙ′ R (const×⊤ₙ [])
    []ₙ⁺ = []ₙ

    _++ₙ⁺_ :
      ∀ {s t} {us : Product⊤ n (smap id (λ A → Vector A s) n As)}
      {vs : Product⊤ n (smap id (λ A → Vector A t) n As)} →
      Liftₙ′ R us → Liftₙ′ R vs →
      Liftₙ′ R (zipWith×⊤ₙ _++_ us vs)
    _++ₙ⁺_ {s} {t} ru rv =
      (mk λ i → map×⊤ₙ←∘map×⊤ₙ-← n (uncurry⊤ₙ n R) (lemma-u R (ru .get i)))
        ++ₙ
      (mk λ i → map×⊤ₙ←∘map×⊤ₙ-← n (uncurry⊤ₙ n R) (lemma-v R (rv .get i)))
      where
      lemma-u : ∀ {n as} {As : Sets n as} (R : As ⇉ Set r)
        {us : Product⊤ n (smap id (λ A → Vector A s) n As)}
        {vs : Product⊤ n (smap id (λ A → Vector A t) n As)} {i} →
        uncurry⊤ₙ n R (map×⊤ₙ← (_$ i) n us) →
        uncurry⊤ₙ n R (map×⊤ₙ← (_$ ↙ i) n (zipWith×⊤ₙ _++_ us vs))
      lemma-u {zero} R r = r
      lemma-u {suc n} R r = lemma-u {n} (R _) r

      lemma-v : ∀ {n as} {As : Sets n as} (R : As ⇉ Set r)
        {us : Product⊤ n (smap id (λ A → Vector A s) n As)}
        {vs : Product⊤ n (smap id (λ A → Vector A t) n As)} {i} →
        uncurry⊤ₙ n R (map×⊤ₙ← (_$ i) n vs) →
        uncurry⊤ₙ n R (map×⊤ₙ← (_$ ↘ i) n (zipWith×⊤ₙ _++_ us vs))
      lemma-v {zero} R r = r
      lemma-v {suc n} R r = lemma-v {n} (R _) r

    -- We have a kind of pattern-matching for Liftₙ inhabitants.

    un[-]ₙ : {vs : Product⊤ n (smap id (λ A → Vector A [-]) n As)} →
      Liftₙ′ R vs → uncurry⊤ₙ n R (map×⊤ₙ← (_$ here) n vs)
    un[-]ₙ r = r .get here

    un++ₙ :
      ∀ {s t} {vs : Product⊤ n (smap id (λ A → Vector A (s <+> t)) n As)} →
      Liftₙ′ R vs →
      Liftₙ′ R (map×⊤ₙ (_∘ ↙) n vs) × Liftₙ′ R (map×⊤ₙ (_∘ ↘) n vs)
    un++ₙ r .proj₁ .get i =
      map×⊤ₙ←∘map×⊤ₙ-← n (uncurry⊤ₙ n R) (r .get (↙ i))
    un++ₙ r .proj₂ .get j =
      map×⊤ₙ←∘map×⊤ₙ-← n (uncurry⊤ₙ n R) (r .get (↘ j))

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
    setoid S s ._≈_ = Liftₙ (S ._≈_)
    setoid S s .isEquivalence .refl .get i = S .refl
    setoid S s .isEquivalence .sym p .get i = S .sym (p .get i)
    setoid S s .isEquivalence .trans p q .get i =
      S .trans (p .get i) (q .get i)

    [-]ˢ : ∀ {S} → S ⟶ setoid {a} {ℓ} S [-]
    [-]ˢ ._⟨$⟩_ = [_]
    [-]ˢ .cong = [_]ₙ

    []ˢ : ∀ {S} → ⊤.setoid ⊤ 0ℓ ⟶ setoid {a} {ℓ} S ε
    []ˢ ⟨$⟩ _ = []
    []ˢ .cong _ = []ₙ

    ++ˢ : ∀ {S} →
          ×-setoid (setoid S s) (setoid S t) ⟶ setoid {a} {ℓ} S (s <+> t)
    ++ˢ ⟨$⟩ (xs , ys) = xs ++ ys
    ++ˢ .cong (p , q) = p ++ₙ q

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
    []₁∼ .get ()

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
    []₁η refl .get ()

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

  private
    -- Here's an alternative way to define Liftₙ, with less uncurrying.
    -- I haven't decided how it compares to the one I'm actually using.
    -- It is more symmetrical, but I don't know how well it unifies.

    record Liftₙ′0 {n as r} {As : Sets n as} (R : Product⊤ n As → Set r)
      {s} (vs : Product⊤ n (smap id (λ A → Vector A s) n As)) : Set r where
      constructor mk
      field get : ∀ (i : Ptr s) → R (map×⊤ₙ← (_$ i) n vs)
    open Liftₙ′0  -- public

    Liftₙ0 : ∀ {n as r} {As : Sets n as} (R : As ⇉ Set r) {s} →
      smap id (λ A → Vector A s) n As ⇉ Set r
    Liftₙ0 {n} R = curry⊤ₙ n (Liftₙ′0 (uncurry⊤ₙ n R))

    module _ {n as r} {As : Sets n as} {R : Product⊤ n As → Set r} where

      _++ₙ0_ :
        ∀ {s t} {vs : Product⊤ n (smap id (λ A → Vector A (s <+> t)) n As)} →
        Liftₙ′0 R (map×⊤ₙ (_∘ ↙) n vs) → Liftₙ′0 R (map×⊤ₙ (_∘ ↘) n vs) →
        Liftₙ′0 R vs
      (ru ++ₙ0 rv) .get (↙ i) = map×⊤ₙ←∘map×⊤ₙ-→ n R _ _ _ (ru .get i)
      (ru ++ₙ0 rv) .get (↘ i) = map×⊤ₙ←∘map×⊤ₙ-→ n R _ _ _ (rv .get i)

      _++ₙ⁺0_ :
        ∀ {s t} {us : Product⊤ n (smap id (λ A → Vector A s) n As)}
        {vs : Product⊤ n (smap id (λ A → Vector A t) n As)} →
        Liftₙ′0 R us → Liftₙ′0 R vs →
        Liftₙ′0 R (zipWith×⊤ₙ _++_ us vs)
      _++ₙ⁺0_ {s} {t} ru rv =
        (mk λ i → map×⊤ₙ←∘map×⊤ₙ-← n R (lemma-u R (ru .get i))) ++ₙ0
        (mk λ i → map×⊤ₙ←∘map×⊤ₙ-← n R (lemma-v R (rv .get i)))
        where
        lemma-u : ∀ {n as} {As : Sets n as} (R : Product⊤ n As → Set r)
          {us : Product⊤ n (smap id (λ A → Vector A s) n As)}
          {vs : Product⊤ n (smap id (λ A → Vector A t) n As)} {i} →
          R (map×⊤ₙ← (_$ i) n us) → R (map×⊤ₙ← (_$ ↙ i) n (zipWith×⊤ₙ _++_ us vs))
        lemma-u {zero} R r = r
        lemma-u {suc n} R r = lemma-u {n} (λ xs → R (_ , xs)) r

        lemma-v : ∀ {n as} {As : Sets n as} (R : Product⊤ n As → Set r)
          {us : Product⊤ n (smap id (λ A → Vector A s) n As)}
          {vs : Product⊤ n (smap id (λ A → Vector A t) n As)} {i} →
          R (map×⊤ₙ← (_$ i) n vs) → R (map×⊤ₙ← (_$ ↘ i) n (zipWith×⊤ₙ _++_ us vs))
        lemma-v {zero} R r = r
        lemma-v {suc n} R r = lemma-v {n} (λ xs → R (_ , xs)) r
