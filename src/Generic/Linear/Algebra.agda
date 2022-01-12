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
  1ᴿ .rel x y = y ≤* x
  1ᴿ .rel-≤ₘ xx yy r = ≤*-trans yy (≤*-trans r xx)
  1ᴿ .rel-0ₘ (sp0 , r) = 0ₘ-mono r sp0
  1ᴿ .rel-+ₘ (sp+ , r) = ≤*-refl ↘, +ₘ-mono r ≤*-refl ≤*-refl sp+ ,↙ ≤*-refl
  1ᴿ .rel-*ₘ (sp* , r) = ≤*-refl , *ₘ-mono r ≤-refl ≤*-refl sp*
  1ᴿ .func x = ≤*-refl , id

  _>>ᴿ_ : ∀ {a b s t u} →
    LinFuncRel s t a → LinFuncRel t u b → LinFuncRel s u (a ⊔ b)
  (F >>ᴿ G) .rel x z = (x ⟨ F .rel ⟩_) ◇ (_⟨ G .rel ⟩ z)
  (F >>ᴿ G) .rel-≤ₘ xx zz (f , g) =
    F .rel-≤ₘ xx ≤*-refl f , G .rel-≤ₘ ≤*-refl zz g
  (F >>ᴿ G) .rel-0ₘ (sp0 , (f , g)) = G .rel-0ₘ (F .rel-0ₘ (sp0 , f) , g)
  (F >>ᴿ G) .rel-+ₘ (sp+ , (f , g)) =
    let fl ↘, sp+f ,↙ fr = F .rel-+ₘ (sp+ , f) in
    let gl ↘, sp+g ,↙ gr = G .rel-+ₘ (sp+f , g) in
    (fl , gl) ↘, sp+g ,↙ (fr , gr)
  (F >>ᴿ G) .rel-*ₘ (sp* , (f , g)) =
    let f′ , sp*f = F .rel-*ₘ (sp* , f) in
    let g′ , sp*g = G .rel-*ₘ (sp*f , g) in
    (f′ , g′) , sp*g
  (F >>ᴿ G) .func x =
    let _,_ {y} f uy = F .func x in
    let g , uz = G .func y in
    (f , g) , λ (f′ , g′) → uz (G .rel-≤ₘ (uy f′) ≤*-refl g′)

  -- Parallel addition

  0ᴿ : ∀ {s t} → LinFuncRel s t 0ℓ
  0ᴿ .rel x y = y ≤0ₘ
  0ᴿ .rel-≤ₘ xx yy le0 = 0ₘ-mono yy le0
  0ᴿ .rel-0ₘ (sp0 , le0) = le0
  0ᴿ .rel-+ₘ (sp+ , le0) = +ₘ-identity²← le0
  0ᴿ .rel-*ₘ (sp* , le0) = swap-◇ (*ₘ-annihilʳ← le0)
  0ᴿ .func x = 0*-triv , 0*→≤*

  _+ᴿ_ : ∀ {a b s t} →
    LinFuncRel s t a → LinFuncRel s t b → LinFuncRel s t (a ⊔ b)
  (F +ᴿ G) .rel x y = F .rel x ↘- y ≤[_+ₘ_] -↙ G .rel x
  (F +ᴿ G) .rel-≤ₘ xx yy (f ↘, sp ,↙ g) =
    F .rel-≤ₘ xx ≤*-refl f
      ↘, +ₘ-mono yy ≤*-refl ≤*-refl sp ,↙
    G .rel-≤ₘ xx ≤*-refl g
  (F +ᴿ G) .rel-0ₘ (sp0 , (f ↘, sp ,↙ g)) =
    +ₘ-identity²→ (F .rel-0ₘ (sp0 , f) ↘, sp ,↙ G .rel-0ₘ (sp0 , g))
  (F +ᴿ G) .rel-+ₘ (sp+ , (f ↘, sp ,↙ g)) =
    let fl ↘, spf ,↙ fr = F .rel-+ₘ (sp+ , f) in
    let gl ↘, spg ,↙ gr = G .rel-+ₘ (sp+ , g) in
    let spl ↘, sp′ ,↙ spr = +ₘ-inter (spf ↘, sp ,↙ spg) in
    (fl ↘, spl ,↙ gl) ↘, sp′ ,↙ (fr ↘, spr ,↙ gr)
  (F +ᴿ G) .rel-*ₘ (sp* , (f ↘, sp ,↙ g)) =
    let f′ , spf = F .rel-*ₘ (sp* , f) in
    let g′ , spg = G .rel-*ₘ (sp* , g) in
    let sp*′ , sp′ = *ₘ-distribʳ← (spf ↘, sp ,↙ spg) in
    (f′ ↘, sp′ ,↙ g′) , sp*′
  (F +ᴿ G) .func x =
    let f , uf = F .func x in
    let g , ug = G .func x in
    (f ↘, +*-triv ,↙ g) , λ (f′ ↘, sp′ ,↙ g′) →
      +*→≤* (+ₘ-mono ≤*-refl (uf f′) (ug g′) sp′)

  -- Shape
  --  Vertical

  [─]ᴿ : ∀ {u} → LinFuncRel ε u 0ℓ
  [─]ᴿ = 0ᴿ

  [_─_]ᴿ : ∀ {a b s t u} →
    LinFuncRel s u a → LinFuncRel t u b → LinFuncRel (s <+> t) u (a ⊔ b)
  [ F ─ G ]ᴿ .rel x y = F .rel (x ∘ ↙) ↘- y ≤[_+ₘ_] -↙ G .rel (x ∘ ↘)
  [ F ─ G ]ᴿ .rel-≤ₘ (mk xx) yy (f ↘, f+g ,↙ g) =
    F .rel-≤ₘ (mk (xx ∘ ↙)) ≤*-refl f
    ↘, +ₘ-mono yy ≤*-refl ≤*-refl f+g ,↙
    G .rel-≤ₘ (mk (xx ∘ ↘)) ≤*-refl g
  [ F ─ G ]ᴿ .rel-0ₘ (sp0 , (f ↘, f+g ,↙ g)) =
    let sp0f , sp0g = un++ₙ sp0 in
    +ₘ-identity²→ (F .rel-0ₘ (sp0f , f) ↘, f+g ,↙ G .rel-0ₘ (sp0g , g))
  [ F ─ G ]ᴿ .rel-+ₘ (sp+ , (f ↘, f+g ,↙ g)) =
    let sp+f , sp+g = un++ₙ sp+ in
    let fl ↘, sp+f′ ,↙ fr = F .rel-+ₘ (sp+f , f) in
    let gl ↘, sp+g′ ,↙ gr = G .rel-+ₘ (sp+g , g) in
    let sp+r₂ ↘, l+r ,↙ sp+s₂ = +ₘ-inter (sp+f′ ↘, f+g ,↙ sp+g′) in
    (fl ↘, sp+r₂ ,↙ gl) ↘, l+r ,↙ (fr ↘, sp+s₂ ,↙ gr)
  [ F ─ G ]ᴿ .rel-*ₘ (sp* , (f ↘, f+g ,↙ g)) =
    let sp*f , sp*g = un++ₙ sp* in
    let f′ , sp*f′ = F .rel-*ₘ (sp*f , f) in
    let g′ , sp*g′ = G .rel-*ₘ (sp*g , g) in
    let sp*′ , l+r = *ₘ-distribʳ← (sp*f′ ↘, f+g ,↙ sp*g′) in
    (f′ ↘, l+r ,↙ g′) , sp*′
  [ F ─ G ]ᴿ .func x =
    let f , uf = F .func (x ∘ ↙) in
    let g , ug = G .func (x ∘ ↘) in
    (f ↘, +*-triv ,↙ g) , λ (f′ ↘, sp′ ,↙ g′) →
      +*→≤* (+ₘ-mono ≤*-refl (uf f′) (ug g′) sp′)

  [─_─]ᴿ : ∀ {u} → Vector Ann u → LinFuncRel [-] u 0ℓ
  [─ y′ ─]ᴿ .rel x y = y ≤[ x here *ₘ y′ ]
  [─ y′ ─]ᴿ .rel-≤ₘ (mk xx) yy sp = *ₘ-mono yy (xx here) ≤*-refl sp
  [─ y′ ─]ᴿ .rel-0ₘ (sp0 , sp) = *ₘ-annihilˡ→ (sp0 .get here , sp)
  [─ y′ ─]ᴿ .rel-+ₘ (sp+ , sp) = *ₘ-distribˡ→ (sp+ .get here , sp)
  [─ y′ ─]ᴿ .rel-*ₘ (sp* , sp) = swap-◇ (*ₘ-assoc→ (sp* .get here , sp))
  [─ y′ ─]ᴿ .func x = *ₗ-triv , *ₗ→≤*

  topᴿ : ∀ {a s t u} → LinFuncRel (s <+> t) u a → LinFuncRel s u a
  topᴿ F .rel x y = F .rel (x ++ 0*) y
  topᴿ F .rel-≤ₘ xx yy = F .rel-≤ₘ (xx ++ₙ ≤*-refl) yy
  topᴿ F .rel-0ₘ (sp0 , f) = F .rel-0ₘ (sp0 ++ₙ 0*-triv , f)
  topᴿ F .rel-+ₘ (sp+ , f) =
    let _ ↘, sp+0 ,↙ _ = +ₘ-identity²← 0*-triv in
    F .rel-+ₘ (sp+ ++ₙ sp+0 , f)
  topᴿ F .rel-*ₘ (sp* , f) =
    let sp*0 , _ = *ₘ-annihilʳ← 0*-triv in
    F .rel-*ₘ (sp* ++ₙ sp*0 , f)
  topᴿ F .func x = F .func (x ++ 0*)

  botᴿ : ∀ {a s t u} → LinFuncRel (s <+> t) u a → LinFuncRel t u a
  botᴿ F .rel x y = F .rel (0* ++ x) y
  botᴿ F .rel-≤ₘ xx yy = F .rel-≤ₘ (≤*-refl ++ₙ xx) yy
  botᴿ F .rel-0ₘ (sp0 , f) = F .rel-0ₘ (0*-triv ++ₙ sp0 , f)
  botᴿ F .rel-+ₘ (sp+ , f) =
    let _ ↘, sp+0 ,↙ _ = +ₘ-identity²← 0*-triv in
    F .rel-+ₘ (sp+0 ++ₙ sp+ , f)
  botᴿ F .rel-*ₘ (sp* , f) =
    let sp*0 , _ = *ₘ-annihilʳ← 0*-triv in
    F .rel-*ₘ (sp*0 ++ₙ sp* , f)
  botᴿ F .func x = F .func (0* ++ x)

  --  Horizontal

  [│]ᴿ : ∀ {s} → LinFuncRel s ε 0ℓ
  [│]ᴿ .rel _ _ = ⊤
  [│]ᴿ .rel-≤ₘ _ _ _ = _
  [│]ᴿ .rel-0ₘ _ = []ₙ
  [│]ᴿ .rel-+ₘ _ = _↘,_,↙_ {left = []} {[]} _ []ₙ _
  [│]ᴿ .rel-*ₘ _ = _,_ {middle = []} _ []ₙ
  [│]ᴿ .func _ = _,_ {witness = []} _ (λ _ → []ₙ)

  [_│_]ᴿ : ∀ {a b s t u} →
    LinFuncRel s t a → LinFuncRel s u b → LinFuncRel s (t <+> u) (a ⊔ b)
  [ F │ G ]ᴿ .rel x y = F .rel x (y ∘ ↙) × G .rel x (y ∘ ↘)
  [ F │ G ]ᴿ .rel-≤ₘ xx (mk yy) (ll , rr) =
    F .rel-≤ₘ xx (mk (yy ∘ ↙)) ll , G .rel-≤ₘ xx (mk (yy ∘ ↘)) rr
  [ F │ G ]ᴿ .rel-0ₘ (sp0 , (ll , rr)) =
    F .rel-0ₘ (sp0 , ll) ++ₙ G .rel-0ₘ (sp0 , rr)
  [ F │ G ]ᴿ .rel-+ₘ (sp+ , (ll , rr)) =
    let llF ↘, sp+F ,↙ rrF = F .rel-+ₘ (sp+ , ll) in
    let llG ↘, sp+G ,↙ rrG = G .rel-+ₘ (sp+ , rr) in
    _↘,_,↙_ {left = _ ++ _} {_ ++ _} (llF , llG) (sp+F ++ₙ sp+G) (rrF , rrG)
  [ F │ G ]ᴿ .rel-*ₘ (sp* , (ll , rr)) =
    let llF , sp*F = F .rel-*ₘ (sp* , ll) in
    let rrG , sp*G = G .rel-*ₘ (sp* , rr) in
    _,_ {middle = _ ++ _} (llF , rrG) (sp*F ++ₙ sp*G)
  [ F │ G ]ᴿ .func x =
    let f , uf = F .func x in
    let g , ug = G .func x in
    _,_ {witness = _ ++ _} (f , g) (λ (f′ , g′) → uf f′ ++ₙ ug g′)

  [│_│]ᴿ : ∀ {s} → Vector Ann s → LinFuncRel s [-] 0ℓ
  [│_│]ᴿ {[-]} x′ .rel x y = y here ≤[ x here * x′ here ]
  [│_│]ᴿ {ε} x′ .rel x y = y ≤0ₘ
  [│_│]ᴿ {sl <+> sr} x′ .rel x y =
    [│ x′ ∘ ↙ │]ᴿ .rel (x ∘ ↙) ↘- y ≤[_+ₘ_] -↙ [│ x′ ∘ ↘ │]ᴿ .rel (x ∘ ↘)
  [│_│]ᴿ {[-]} x′ .rel-≤ₘ (mk xx) (mk yy) r =
    *-mono↔ (yy here) (xx here) ≤-refl r
  [│_│]ᴿ {ε} x′ .rel-≤ₘ xx yy sp = 0ₘ-mono yy sp
  [│_│]ᴿ {sl <+> sr} x′ .rel-≤ₘ xx yy (l ↘, sp ,↙ r) =
    let xx↙ , xx↘ = un++ₙ xx in
    [│ x′ ∘ ↙ │]ᴿ .rel-≤ₘ xx↙ ≤*-refl l
    ↘, +ₘ-mono yy ≤*-refl ≤*-refl sp ,↙
    [│ x′ ∘ ↘ │]ᴿ .rel-≤ₘ xx↘ ≤*-refl r
  [│_│]ᴿ {[-]} x′ .rel-0ₘ (mk sp0 , r) = [ annihilˡ→ (sp0 here , r) ]ₙ
  [│_│]ᴿ {ε} x′ .rel-0ₘ (mk sp0 , sp) = sp
  [│_│]ᴿ {sl <+> sr} x′ .rel-0ₘ (mk sp0 , (l ↘, mk sp ,↙ r)) =
    let mk sp0l = [│ x′ ∘ ↙ │]ᴿ .rel-0ₘ (mk (sp0 ∘ ↙) , l) in
    let mk sp0r = [│ x′ ∘ ↘ │]ᴿ .rel-0ₘ (mk (sp0 ∘ ↘) , r) in
    [ +-identity²→ (sp0l here ↘, sp here ,↙ sp0r here) ]ₙ
  [│_│]ᴿ {[-]} x′ .rel-+ₘ (mk sp+ , r) =
    let ll ↘, sp+′ ,↙ rr = distribˡ→ (sp+ here , r) in
    _↘,_,↙_ {left = [ _ ]} {[ _ ]} ll [ sp+′ ]ₙ rr
  [│_│]ᴿ {ε} x′ .rel-+ₘ (mk sp+ , mk r) =
    let ll ↘, sp+′ ,↙ rr = +-identity²← (r here) in
    _↘,_,↙_ {left = [ _ ]} {[ _ ]} [ ll ]ₙ [ sp+′ ]ₙ [ rr ]ₙ
  [│_│]ᴿ {sl <+> sr} x′ .rel-+ₘ (mk sp+ , (l ↘, mk sp ,↙ r)) =
    let ll ↘, mk sp+l ,↙ rl = [│ x′ ∘ ↙ │]ᴿ .rel-+ₘ (mk (sp+ ∘ ↙) , l) in
    let lr ↘, mk sp+r ,↙ rr = [│ x′ ∘ ↘ │]ᴿ .rel-+ₘ (mk (sp+ ∘ ↘) , r) in
    let sp+l′ ↘, sp+′ ,↙ sp+r′ = +-inter↔ (sp+l here ↘, sp here ,↙ sp+r here) in
    _↘,_,↙_ {left = [ _ ]} {[ _ ]}
      (ll ↘, [ sp+l′ ]ₙ ,↙ lr) [ sp+′ ]ₙ (rl ↘, [ sp+r′ ]ₙ ,↙ rr)
  [│_│]ᴿ {[-]} x′ .rel-*ₘ (mk sp* , r) =
    let r′ , sp*′ = *-assoc→ (sp* here , r) in
    _,_ {middle = [ _ ]} sp*′ [ r′ ]ₙ
  [│_│]ᴿ {ε} x′ .rel-*ₘ (mk sp* , mk sp) =
    let sp*′ , sp′ = annihilʳ← (sp here) in
    _,_ {middle = [ _ ]} [ sp′ ]ₙ [ sp*′ ]ₙ
  [│_│]ᴿ {sl <+> sr} x′ .rel-*ₘ (mk sp* , (l ↘, mk sp ,↙ r)) =
    let l′ , mk sp*l = [│ x′ ∘ ↙ │]ᴿ .rel-*ₘ (mk (sp* ∘ ↙) , l) in
    let r′ , mk sp*r = [│ x′ ∘ ↘ │]ᴿ .rel-*ₘ (mk (sp* ∘ ↘) , r) in
    let sp*′ , sp′ = distribʳ← (sp*l here ↘, sp here ,↙ sp*r here) in
    _,_ {middle = [ _ ]} (l′ ↘, [ sp′ ]ₙ ,↙ r′) [ sp*′ ]ₙ
  [│_│]ᴿ {[-]} x′ .func x = _,_ {witness = [ _ ]} ≤-refl (λ r′ → *ₗ→≤* [ r′ ]ₙ)
  [│_│]ᴿ {ε} x′ .func x = 0*-triv , 0*→≤*
  [│_│]ᴿ {sl <+> sr} x′ .func x =
    let l , ul = [│ x′ ∘ ↙ │]ᴿ .func (x ∘ ↙) in
    let r , ur = [│ x′ ∘ ↘ │]ᴿ .func (x ∘ ↘) in
    (l ↘, +*-triv ,↙ r) , λ (l′ ↘, sp′ ,↙ r′) →
      +*→≤* (+ₘ-mono ≤*-refl (ul l′) (ur r′) sp′)

  -- Compound

  _⊕ᴿ_ : ∀ {a b sl sr tl tr} → LinFuncRel sl tl a → LinFuncRel sr tr b →
    LinFuncRel (sl <+> sr) (tl <+> tr) (a ⊔ b)
  (F ⊕ᴿ G) .rel x y = F .rel (x ∘ ↙) (y ∘ ↙) × G .rel (x ∘ ↘) (y ∘ ↘)
  (F ⊕ᴿ G) .rel-≤ₘ (mk xx) (mk yy) (ll , rr) =
    F .rel-≤ₘ (mk (xx ∘ ↙)) (mk (yy ∘ ↙)) ll ,
    G .rel-≤ₘ (mk (xx ∘ ↘)) (mk (yy ∘ ↘)) rr
  (F ⊕ᴿ G) .rel-0ₘ (mk sp0 , (ll , rr)) =
    F .rel-0ₘ (mk (sp0 ∘ ↙) , ll) ++ₙ G .rel-0ₘ (mk (sp0 ∘ ↘) , rr)
  (F ⊕ᴿ G) .rel-+ₘ (mk sp+ , (ll , rr)) =
    let llF ↘, sp+F ,↙ rrF = F .rel-+ₘ (mk (sp+ ∘ ↙) , ll) in
    let llG ↘, sp+G ,↙ rrG = G .rel-+ₘ (mk (sp+ ∘ ↘) , rr) in
    _↘,_,↙_ {left = _ ++ _} {_ ++ _}
      (llF , llG) (sp+F ++ₙ sp+G) (rrF , rrG)
  (F ⊕ᴿ G) .rel-*ₘ (mk sp* , (ll , rr)) =
    let llF , sp*F = F .rel-*ₘ (mk (sp* ∘ ↙) , ll) in
    let rrG , sp*G = G .rel-*ₘ (mk (sp* ∘ ↘) , rr) in
    _,_ {middle = _ ++ _} (llF , rrG) (sp*F ++ₙ sp*G)
  (F ⊕ᴿ G) .func x =
    let f , uf = F .func (x ∘ ↙) in
    let g , ug = G .func (x ∘ ↘) in
    _,_ {witness = _ ++ _} (f , g) (λ (f′ , g′) → uf f′ ++ₙ ug g′)
