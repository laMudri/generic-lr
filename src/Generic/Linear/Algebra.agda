{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Po
open import Level using (0ℓ; suc; _⊔_)

module Generic.Linear.Algebra (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ) where

  open PoSemiring poSemiring renaming (Carrier to Ann)

  open import Algebra.Po.Construct.Vector as APCV
    using (Vector-poLeftSemimodule; id-PoSemiringMor)
  open import Algebra.Relational.Construct.Vector as ARCV
    using (Vector-fRelLeftSemimodule)
  open import Algebra.PoToRel
  open import Algebra.Relational renaming (_↘_↙_ to _↘-_-↙_)
  open import Algebra.Relational.Relation
  open import Data.LTree
  open import Data.LTree.Vector hiding (setoid)
  open import Data.LTree.Vector.Properties
  open import Data.Product
  open import Data.Product.Nary.NonDependent
  open import Data.Unit
  open import Function
  open import Function.Nary.NonDependent
  open import Relation.Binary using (REL; _=[_]⇒_; _⇒_)
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
  open import Relation.Nary

  open import Generic.Linear.Operations rawPoSemiring

  private
    variable
      s t : LTree
      P Q R : Vector Ann s

  ≤*-refl : P ≤* P
  ≤*-refl .get i = ≤-refl
  ≤*-trans : P ≤* Q → Q ≤* R → P ≤* R
  ≤*-trans PQ QR .get i = ≤-trans (PQ .get i) (QR .get i)

  ≈*-refl : P ≈* P
  ≈*-refl .get i = refl
  ≈*-trans : P ≈* Q → Q ≈* R → P ≈* R
  ≈*-trans PQ QR .get i = trans (PQ .get i) (QR .get i)
  ≈*-sym : P ≈* Q → Q ≈* P
  ≈*-sym PQ .get i = sym (PQ .get i)
  ≤*-reflexive : P ≈* Q → P ≤* Q
  ≤*-reflexive PQ .get i = ≤-reflexive (PQ .get i)

  0*-triv : ∀ {s} → 0* {s} ≤0*
  0*-triv .get i = ≤-refl
  +*-triv : P +* Q ≤[ P +* Q ]
  +*-triv .get i = ≤-refl
  *ₗ-triv : ∀ {r} → r *ₗ P ≤[ r *ₗ P ]
  *ₗ-triv .get i = ≤-refl

  -- Conversion between n-ary relations and _≈*_

  ≈*→0* : ∀ {s} {R : Vector _ s} → R ≈* 0* → R ≤0*
  ≈*→0* = ≤*→0* ∘ ≤*-reflexive
  ≈*→+* : ∀ {s} {P Q R : Vector _ s} → R ≈* P +* Q → R ≤[ P +* Q ]
  ≈*→+* = ≤*→+* ∘ ≤*-reflexive
  ≈*→*ₗ : ∀ {s r} {P R : Vector _ s} → R ≈* r *ₗ P → R ≤[ r *ₗ P ]
  ≈*→*ₗ = ≤*→*ₗ ∘ ≤*-reflexive

  -- Addition properties

  -- +*-identity↖ : (P : Vector Ann s) → 0* +* P ≤* P
  -- +*-identity↖ P .get _ = +.identity-→ .proj₁ _
  -- +*-identity↗ : (P : Vector Ann s) → P +* 0* ≤* P
  -- +*-identity↗ P .get _ = +.identity-← .proj₂ _
  +*-identity↙ : (P : Vector Ann s) → P ≤[ 0* +* P ]
  +*-identity↙ P .get _ = +.identity-← .proj₁ _
  +*-identity↘ : (P : Vector Ann s) → P ≤[ P +* 0* ]
  +*-identity↘ P .get _ = +.identity-→ .proj₂ _

  +*-comm : (P Q : Vector Ann s) → P +* Q ≈* Q +* P
  +*-comm P Q .get i = +-comm (P i) (Q i)

  -- LinMor

  open APCV public

  Vᴾ = Vector-poLeftSemimodule poSemiring

  -- LinRel

  Annᶠᴿ : FRelSemiring 0ℓ 0ℓ
  Annᶠᴿ = poSemiring-to-fRelSemiring poSemiring

  Vᶠᴿ : LTree → FRelLeftSemimodule _ 0ℓ 0ℓ
  Vᶠᴿ = Vector-fRelLeftSemimodule Annᶠᴿ
  Vᴿ : LTree → RelLeftSemimodule _ 0ℓ 0ℓ
  Vᴿ s = FRelLeftSemimodule.relLeftSemimodule (Vᶠᴿ s)

  open FRelSemiring Annᶠᴿ public using (_≤0; _≤[_+_]; _≤[_*_])
  open FRelSemiring Annᶠᴿ hiding (_≤0; _≤[_+_]; _≤[_*_]) renaming
    (+-comm to +-comm↔; +-inter to +-inter↔; *-mono to *-mono↔)
  private
    module Dummy {s} = FRelLeftSemimodule (Vᶠᴿ s)
  open Dummy
  open Dummy public using (0ₘ-mono; +ₘ-mono; *ₘ-mono)

  -- LinFuncRel

  LinFuncRel : ∀ (s t : LTree) ℓ → Set _
  LinFuncRel s t ℓ = RelLeftSemimoduleFuncRel (Vᴿ s) (Vᴿ t) ℓ
  open RelLeftSemimoduleFuncRel public

  -- Composition

  1ᴿ : ∀ {s} → LinFuncRel s s 0ℓ
  1ᴿ .rel = _≤*_
  1ᴿ .rel-≤ₘ xx yy r = ≤*-trans xx (≤*-trans r yy)
  1ᴿ .rel-0ₘ (r , sp0) = 0ₘ-mono r sp0
  1ᴿ .rel-+ₘ (r , sp+) = ≤*-refl ↘, +ₘ-mono r ≤*-refl ≤*-refl sp+ ,↙ ≤*-refl
  1ᴿ .rel-*ₘ (r , sp*) = ≤*-refl , *ₘ-mono r ≤-refl ≤*-refl sp*
  1ᴿ .func x = ≤*-refl , id

  _>>ᴿ_ : ∀ {a b s t u} →
    LinFuncRel s t a → LinFuncRel t u b → LinFuncRel s u (a ⊔ b)
  (F >>ᴿ G) .rel x z = (x ⟨ F .rel ⟩_) ◇ (_⟨ G .rel ⟩ z)
  (F >>ᴿ G) .rel-≤ₘ xx zz (f , g) =
    F .rel-≤ₘ xx ≤*-refl f , G .rel-≤ₘ ≤*-refl zz g
  (F >>ᴿ G) .rel-0ₘ ((f , g) , sp0) = F .rel-0ₘ (f , (G .rel-0ₘ (g , sp0)))
  (F >>ᴿ G) .rel-+ₘ ((f , g) , sp+) =
    let gl ↘, sp+g ,↙ gr = G .rel-+ₘ (g , sp+) in
    let fl ↘, sp+f ,↙ fr = F .rel-+ₘ (f , sp+g) in
    (fl , gl) ↘, sp+f ,↙ (fr , gr)
  (F >>ᴿ G) .rel-*ₘ ((f , g) , sp*) =
    let g′ , sp*g = G .rel-*ₘ (g , sp*) in
    let f′ , sp*f = F .rel-*ₘ (f , sp*g) in
    (f′ , g′) , sp*f
  (F >>ᴿ G) .func z =
    let _,_ {y} g uy = G .func z in
    let f , ux = F .func y in
    (f , g) , λ (f′ , g′) → ux (F .rel-≤ₘ ≤*-refl (uy g′) f′)

  -- Pointwise operations

  0ᴿ : ∀ {s t} → LinFuncRel s t 0ℓ
  0ᴿ .rel x y = x ≤0ₘ
  0ᴿ .rel-≤ₘ xx yy le0 = 0ₘ-mono xx le0
  0ᴿ .rel-0ₘ (le0 , sp0) = le0
  0ᴿ .rel-+ₘ (le0 , sp+) = +ₘ-identity²← le0
  0ᴿ .rel-*ₘ (le0 , sp*) = swap-◇ (*ₘ-annihilʳ← le0)
  0ᴿ .func x = 0*-triv , 0*→≤*

  _+ᴿ_ : ∀ {a b s t} →
    LinFuncRel s t a → LinFuncRel s t b → LinFuncRel s t (a ⊔ b)
  (F +ᴿ G) .rel x y = flip (F .rel) y ↘- x ≤[_+ₘ_] -↙ flip (G .rel) y
  (F +ᴿ G) .rel-≤ₘ xx yy (f ↘, sp ,↙ g) =
    F .rel-≤ₘ ≤*-refl yy f
      ↘, +ₘ-mono xx ≤*-refl ≤*-refl sp ,↙
    G .rel-≤ₘ ≤*-refl yy g
  (F +ᴿ G) .rel-0ₘ ((f ↘, sp ,↙ g) , sp0) =
    +ₘ-identity²→ (F .rel-0ₘ (f , sp0) ↘, sp ,↙ G .rel-0ₘ (g , sp0))
  (F +ᴿ G) .rel-+ₘ ((f ↘, sp ,↙ g) , sp+) =
    let fl ↘, spf ,↙ fr = F .rel-+ₘ (f , sp+) in
    let gl ↘, spg ,↙ gr = G .rel-+ₘ (g , sp+) in
    let spl ↘, sp′ ,↙ spr = +ₘ-inter (spf ↘, sp ,↙ spg) in
    (fl ↘, spl ,↙ gl) ↘, sp′ ,↙ (fr ↘, spr ,↙ gr)
  (F +ᴿ G) .rel-*ₘ ((f ↘, sp ,↙ g) , sp*) =
    let f′ , spf = F .rel-*ₘ (f , sp*) in
    let g′ , spg = G .rel-*ₘ (g , sp*) in
    let sp*′ , sp′ = *ₘ-distribʳ← (spf ↘, sp ,↙ spg) in
    (f′ ↘, sp′ ,↙ g′) , sp*′
  (F +ᴿ G) .func y =
    let f , uf = F .func y in
    let g , ug = G .func y in
    (f ↘, +*-triv ,↙ g) , λ (f′ ↘, sp′ ,↙ g′) →
      +*→≤* (+ₘ-mono ≤*-refl (uf f′) (ug g′) sp′)

  -- Shape
  --  Vertical

  [─]ᴿ : ∀ {s} → LinFuncRel s ε 0ℓ
  [─]ᴿ = 0ᴿ

  [_─_]ᴿ : ∀ {a b s t u} →
    LinFuncRel s t a → LinFuncRel s u b → LinFuncRel s (t <+> u) (a ⊔ b)
  [ F ─ G ]ᴿ .rel x y =
    flip (F .rel) (y ∘ ↙) ↘- x ≤[_+ₘ_] -↙ flip (G .rel) (y ∘ ↘)
  [ F ─ G ]ᴿ .rel-≤ₘ xx (mk yy) (f ↘, f+g ,↙ g) =
    F .rel-≤ₘ ≤*-refl (mk (yy ∘ ↙)) f
      ↘, +ₘ-mono xx ≤*-refl ≤*-refl f+g ,↙
    G .rel-≤ₘ ≤*-refl (mk (yy ∘ ↘)) g
  [ F ─ G ]ᴿ .rel-0ₘ ((f ↘, f+g ,↙ g) , sp0) =
    let sp0f , sp0g = un++ₙ sp0 in
    +ₘ-identity²→ (F .rel-0ₘ (f , sp0f) ↘, f+g ,↙ G .rel-0ₘ (g , sp0g))
  [ F ─ G ]ᴿ .rel-+ₘ ((f ↘, f+g ,↙ g) , sp+) =
    let sp+f , sp+g = un++ₙ sp+ in
    let fl ↘, sp+f′ ,↙ fr = F .rel-+ₘ (f , sp+f) in
    let gl ↘, sp+g′ ,↙ gr = G .rel-+ₘ (g , sp+g) in
    let sp+r₂ ↘, l+r ,↙ sp+s₂ = +ₘ-inter (sp+f′ ↘, f+g ,↙ sp+g′) in
    (fl ↘, sp+r₂ ,↙ gl) ↘, l+r ,↙ (fr ↘, sp+s₂ ,↙ gr)
  [ F ─ G ]ᴿ .rel-*ₘ ((f ↘, f+g ,↙ g) , sp*) =
    let sp*f , sp*g = un++ₙ sp* in
    let f′ , sp*f′ = F .rel-*ₘ (f , sp*f) in
    let g′ , sp*g′ = G .rel-*ₘ (g , sp*g) in
    let sp*′ , l+r = *ₘ-distribʳ← (sp*f′ ↘, f+g ,↙ sp*g′) in
    (f′ ↘, l+r ,↙ g′) , sp*′
  [ F ─ G ]ᴿ .func y =
    let f , uf = F .func (y ∘ ↙) in
    let g , ug = G .func (y ∘ ↘) in
    (f ↘, +*-triv ,↙ g) , λ (f′ ↘, sp′ ,↙ g′) →
      +*→≤* (+ₘ-mono ≤*-refl (uf f′) (ug g′) sp′)

  [─_─]ᴿ : ∀ {s} → Vector Ann s → LinFuncRel s [-] 0ℓ
  [─ x′ ─]ᴿ .rel x y = x ≤[ y here *ₘ x′ ]
  [─ x′ ─]ᴿ .rel-≤ₘ xx (mk yy) sp = *ₘ-mono xx (yy here) ≤*-refl sp
  [─ x′ ─]ᴿ .rel-0ₘ (sp , sp0) = *ₘ-annihilˡ→ (sp0 .get here , sp)
  [─ x′ ─]ᴿ .rel-+ₘ (sp , sp+) = *ₘ-distribˡ→ (sp+ .get here , sp)
  [─ x′ ─]ᴿ .rel-*ₘ (sp , sp*) = swap-◇ (*ₘ-assoc→ (sp* .get here , sp))
  [─ x′ ─]ᴿ .func y = *ₗ-triv , *ₗ→≤*

  --  Horizontal

  [│]ᴿ : ∀ {u} → LinFuncRel ε u 0ℓ
  [│]ᴿ .rel _ _ = ⊤
  [│]ᴿ .rel-≤ₘ _ _ _ = _
  [│]ᴿ .rel-0ₘ _ = []ₙ
  [│]ᴿ .rel-+ₘ _ = _↘,_,↙_ {left = []} {[]} _ []ₙ _
    -- Can't use []ₙ⁺ because middle is already known.
  [│]ᴿ .rel-*ₘ _ = _,_ {middle = []} _ []ₙ
  [│]ᴿ .func _ = _,_ {witness = []} _ (λ _ → []ₙ)

  [_│_]ᴿ : ∀ {a b s t u} →
    LinFuncRel s u a → LinFuncRel t u b → LinFuncRel (s <+> t) u (a ⊔ b)
  [ F │ G ]ᴿ .rel x y = F .rel (x ∘ ↙) y × G .rel (x ∘ ↘) y
  [ F │ G ]ᴿ .rel-≤ₘ (mk xx) yy (ll , rr) =
    F .rel-≤ₘ (mk (xx ∘ ↙)) yy ll , G .rel-≤ₘ (mk (xx ∘ ↘)) yy rr
  [ F │ G ]ᴿ .rel-0ₘ ((ll , rr) , sp0) =
    F .rel-0ₘ (ll , sp0) ++ₙ G .rel-0ₘ (rr , sp0)
  [ F │ G ]ᴿ .rel-+ₘ ((ll , rr) , sp+) =
    let llF ↘, sp+F ,↙ rrF = F .rel-+ₘ (ll , sp+) in
    let llG ↘, sp+G ,↙ rrG = G .rel-+ₘ (rr , sp+) in
    _↘,_,↙_ {left = _ ++ _} {_ ++ _} (llF , llG) (sp+F ++ₙ sp+G) (rrF , rrG)
  [ F │ G ]ᴿ .rel-*ₘ ((ll , rr) , sp*) =
    let llF , sp*F = F .rel-*ₘ (ll , sp*) in
    let rrG , sp*G = G .rel-*ₘ (rr , sp*) in
    _,_ {middle = _ ++ _} (llF , rrG) (sp*F ++ₙ sp*G)
  [ F │ G ]ᴿ .func x =
    let f , uf = F .func x in
    let g , ug = G .func x in
    _,_ {witness = _ ++ _} (f , g) (λ (f′ , g′) → uf f′ ++ₙ ug g′)

  [│_│]ᴿ : ∀ {s} → Vector Ann s → LinFuncRel [-] s 0ℓ
  [│_│]ᴿ {[-]} y′ .rel x y = x here ≤[ y here * y′ here ]
  [│_│]ᴿ {ε} y′ .rel x y = x ≤0ₘ
  [│_│]ᴿ {s <+> t} y′ .rel x y =
    flip ([│ y′ ∘ ↙ │]ᴿ .rel) (y ∘ ↙)
      ↘- x ≤[_+ₘ_] -↙
    flip ([│ y′ ∘ ↘ │]ᴿ .rel) (y ∘ ↘)
  [│_│]ᴿ {[-]} y′ .rel-≤ₘ (mk xx) (mk yy) r =
    *-mono↔ (xx here) (yy here) ≤-refl r
  [│_│]ᴿ {ε} y′ .rel-≤ₘ xx yy sp = 0ₘ-mono xx sp
  [│_│]ᴿ {s <+> s₁} y′ .rel-≤ₘ xx yy (l ↘, sp ,↙ r) =
    let yy↙ , yy↘ = un++ₙ yy in
    [│ y′ ∘ ↙ │]ᴿ .rel-≤ₘ ≤*-refl yy↙ l
      ↘, +ₘ-mono xx ≤*-refl ≤*-refl sp ,↙
    [│ y′ ∘ ↘ │]ᴿ .rel-≤ₘ ≤*-refl yy↘ r
  [│_│]ᴿ {[-]} y′ .rel-0ₘ (r , mk sp0) = [ annihilˡ→ (sp0 here , r) ]ₙ
  [│_│]ᴿ {ε} y′ .rel-0ₘ (sp , mk sp0) = sp
  [│_│]ᴿ {s <+> t} y′ .rel-0ₘ ((l ↘, mk sp ,↙ r) , mk sp0) =
    let mk sp0l = [│ y′ ∘ ↙ │]ᴿ .rel-0ₘ (l , mk (sp0 ∘ ↙)) in
    let mk sp0r = [│ y′ ∘ ↘ │]ᴿ .rel-0ₘ (r , mk (sp0 ∘ ↘)) in
    [ +-identity²→ (sp0l here ↘, sp here ,↙ sp0r here) ]ₙ
  [│_│]ᴿ {[-]} y′ .rel-+ₘ (r , mk sp+) =
    let ll ↘, sp+′ ,↙ rr = distribˡ→ (sp+ here , r) in
    _↘,_,↙_ {left = [ _ ]} {[ _ ]} ll [ sp+′ ]ₙ rr
  [│_│]ᴿ {ε} y′ .rel-+ₘ (mk r , mk sp+) =
    let ll ↘, sp+′ ,↙ rr = +-identity²← (r here) in
    _↘,_,↙_ {left = [ _ ]} {[ _ ]} [ ll ]ₙ [ sp+′ ]ₙ [ rr ]ₙ
  [│_│]ᴿ {s <+> t} y′ .rel-+ₘ ((l ↘, mk sp ,↙ r) , mk sp+) =
    let ll ↘, mk sp+l ,↙ rl = [│ y′ ∘ ↙ │]ᴿ .rel-+ₘ (l , mk (sp+ ∘ ↙)) in
    let lr ↘, mk sp+r ,↙ rr = [│ y′ ∘ ↘ │]ᴿ .rel-+ₘ (r , mk (sp+ ∘ ↘)) in
    let sp+l′ ↘, sp+′ ,↙ sp+r′ = +-inter↔ (sp+l here ↘, sp here ,↙ sp+r here) in
    _↘,_,↙_ {left = [ _ ]} {[ _ ]}
      (ll ↘, [ sp+l′ ]ₙ ,↙ lr) [ sp+′ ]ₙ (rl ↘, [ sp+r′ ]ₙ ,↙ rr)
  [│_│]ᴿ {[-]} y′ .rel-*ₘ (r , mk sp*) =
    let r′ , sp*′ = *-assoc→ (sp* here , r) in
    _,_ {middle = [ _ ]} sp*′ [ r′ ]ₙ
  [│_│]ᴿ {ε} y′ .rel-*ₘ (mk sp , mk sp*) =
    let sp*′ , sp′ = annihilʳ← (sp here) in
    _,_ {middle = [ _ ]} [ sp′ ]ₙ [ sp*′ ]ₙ
  [│_│]ᴿ {s <+> s₁} y′ .rel-*ₘ ((l ↘, mk sp ,↙ r) , mk sp*) =
    let l′ , mk sp*l = [│ y′ ∘ ↙ │]ᴿ .rel-*ₘ (l , mk (sp* ∘ ↙)) in
    let r′ , mk sp*r = [│ y′ ∘ ↘ │]ᴿ .rel-*ₘ (r , mk (sp* ∘ ↘)) in
    let sp*′ , sp′ = distribʳ← (sp*l here ↘, sp here ,↙ sp*r here) in
    _,_ {middle = [ _ ]} (l′ ↘, [ sp′ ]ₙ ,↙ r′) [ sp*′ ]ₙ
  [│_│]ᴿ {[-]} y′ .func y = _,_ {witness = [ _ ]} ≤-refl (λ r′ → *ₗ→≤* [ r′ ]ₙ)
  [│_│]ᴿ {ε} y′ .func y = 0*-triv , 0*→≤*
  [│_│]ᴿ {s <+> t} y′ .func y =
    let l , ul = [│ y′ ∘ ↙ │]ᴿ .func (y ∘ ↙) in
    let r , ur = [│ y′ ∘ ↘ │]ᴿ .func (y ∘ ↘) in
    (l ↘, +*-triv ,↙ r) , λ (l′ ↘, sp′ ,↙ r′) →
      +*→≤* (+ₘ-mono ≤*-refl (ul l′) (ur r′) sp′)

  -- Compound

  _⊕ᴿ_ : ∀ {a b sl sr tl tr} → LinFuncRel sl tl a → LinFuncRel sr tr b →
    LinFuncRel (sl <+> sr) (tl <+> tr) (a ⊔ b)
  (F ⊕ᴿ G) .rel x y = F .rel (x ∘ ↙) (y ∘ ↙) × G .rel (x ∘ ↘) (y ∘ ↘)
  (F ⊕ᴿ G) .rel-≤ₘ (mk xx) (mk yy) (ll , rr) =
    F .rel-≤ₘ (mk (xx ∘ ↙)) (mk (yy ∘ ↙)) ll ,
    G .rel-≤ₘ (mk (xx ∘ ↘)) (mk (yy ∘ ↘)) rr
  (F ⊕ᴿ G) .rel-0ₘ ((ll , rr) , mk sp0) =
    F .rel-0ₘ (ll , mk (sp0 ∘ ↙)) ++ₙ G .rel-0ₘ (rr , mk (sp0 ∘ ↘))
  (F ⊕ᴿ G) .rel-+ₘ ((ll , rr) , mk sp+) =
    let llF ↘, sp+F ,↙ rrF = F .rel-+ₘ (ll , mk (sp+ ∘ ↙)) in
    let llG ↘, sp+G ,↙ rrG = G .rel-+ₘ (rr , mk (sp+ ∘ ↘)) in
    _↘,_,↙_ {left = _ ++ _} {_ ++ _}
      (llF , llG) (sp+F ++ₙ sp+G) (rrF , rrG)
  (F ⊕ᴿ G) .rel-*ₘ ((ll , rr) , mk sp*) =
    let llF , sp*F = F .rel-*ₘ (ll , mk (sp* ∘ ↙)) in
    let rrG , sp*G = G .rel-*ₘ (rr , mk (sp* ∘ ↘)) in
    _,_ {middle = _ ++ _} (llF , rrG) (sp*F ++ₙ sp*G)
  (F ⊕ᴿ G) .func x =
    let f , uf = F .func (x ∘ ↙) in
    let g , ug = G .func (x ∘ ↘) in
    _,_ {witness = _ ++ _} (f , g) (λ (f′ , g′) → uf f′ ++ₙ ug g′)
