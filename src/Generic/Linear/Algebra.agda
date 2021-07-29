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

  LinMor : ∀ (s t : LTree) → Set _
  LinMor s t = PoLeftSemimoduleMor id-PoSemiringMor (Vᴾ s) (Vᴾ t)
  open PoLeftSemimoduleMor public

  idLinMor : ∀ {s} → LinMor s s
  idLinMor = 1ᴹ

  _>>_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
    (A → B) → (B → C) → (A → C)
  (f >> g) x = g (f x)

  _>>LinMor_ : ∀ {s t u} → LinMor s t → LinMor t u → LinMor s u
  (F >>LinMor G) .hom = F .hom >> G .hom
  (F >>LinMor G) .hom-cong = F .hom-cong >> G .hom-cong
  (F >>LinMor G) .hom-mono = F .hom-mono >> G .hom-mono
  (F >>LinMor G) .hom-0ₘ = ≈*-trans (G .hom-cong (F .hom-0ₘ)) (G .hom-0ₘ)
  (F >>LinMor G) .hom-+ₘ u v =
    ≈*-trans (G .hom-cong (F .hom-+ₘ _ _)) (G .hom-+ₘ _ _)
  (F >>LinMor G) .hom-*ₘ r u =
    ≈*-trans (G .hom-cong (F .hom-*ₘ _ _)) (G .hom-*ₘ _ _)

  -- LinRel

  Annᶠᴿ : FRelSemiring 0ℓ 0ℓ
  Annᶠᴿ = poSemiring-to-fRelSemiring poSemiring

  Vᶠᴿ : LTree → FRelLeftSemimodule _ 0ℓ 0ℓ
  Vᶠᴿ = Vector-fRelLeftSemimodule Annᶠᴿ
  Vᴿ : LTree → RelLeftSemimodule _ 0ℓ 0ℓ
  Vᴿ s = FRelLeftSemimodule.relLeftSemimodule (Vᶠᴿ s)

  open FRelSemiring Annᶠᴿ renaming
    (+-comm to +-comm↔; +-inter to +-inter↔; *-mono to *-mono↔)
  private open module Dummy {s} = FRelLeftSemimodule (Vᶠᴿ s)

  LinRel : ∀ (s t : LTree) ℓ → Set _
  LinRel s t ℓ = RelLeftSemimoduleRel (Vᴿ s) (Vᴿ t) ℓ
  open RelLeftSemimoduleRel public

  record AsLinRel (M : LinMor s t) ℓ : Set (suc ℓ) where
    field
      linRel : LinRel s t ℓ
      equiv : ∀ {P Q} → linRel .rel P Q ⇔ Q ≤* M .hom P
  open AsLinRel public
  open Equivalence public using () renaming (f to to; g to from)

  idLinRel : ∀ {s} → LinRel s s 0ℓ
  idLinRel .rel x x′ = x′ ≤* x
  idLinRel .rel-≤ₘ xx yy le = ≤*-trans yy (≤*-trans le xx)
  idLinRel .rel-0ₘ (sp0 , le) = 0ₘ-mono le sp0
  idLinRel .rel-+ₘ (sp+ , le) =
    ≤*-refl ↘, +ₘ-mono le ≤*-refl ≤*-refl sp+ ,↙ ≤*-refl
  idLinRel .rel-*ₘ (sp* , le) = *ₘ-mono le ≤-refl ≤*-refl sp* , ≤*-refl

  id⇔ : ∀ {a} {A : Set a} → A ⇔ A
  id⇔ = mk⇔ id id

  idAsLinRel : AsLinRel {s} idLinMor 0ℓ
  idAsLinRel .linRel = idLinRel
  idAsLinRel .equiv = id⇔

  _>>ᴿ_ : ∀ {a b c r s} {A : Set a} {B : Set b} {C : Set c}
    (R : REL A B r) (S : REL B C s) (x : A) (z : C) → Set (b ⊔ r ⊔ s)
  (R >>ᴿ S) x z = (λ y → R x y) ◇ (λ y → S y z)

  _>>LinRel_ : ∀ {a b s t u} → LinRel s t a → LinRel t u b → LinRel s u (a ⊔ b)
  (R >>LinRel S) .rel = R .rel >>ᴿ S .rel
  (R >>LinRel S) .rel-≤ₘ xx yy (r , s) =
    R .rel-≤ₘ xx ≤*-refl r , S .rel-≤ₘ ≤*-refl yy s
  (R >>LinRel S) .rel-0ₘ (sp0 , (r , s)) =
    S .rel-0ₘ (R .rel-0ₘ (sp0 , r) , s)
  (R >>LinRel S) .rel-+ₘ (sp+ , (r , s)) =
    let rl ↘, sp+r ,↙ rr = R .rel-+ₘ (sp+ , r) in
    let sl ↘, sp+s ,↙ sr = S .rel-+ₘ (sp+r , s) in
    (rl , sl) ↘, sp+s ,↙ (rr , sr)
  (R >>LinRel S) .rel-*ₘ (sp* , (r , s)) =
    let sp*r , ri = R .rel-*ₘ (sp* , r) in
    let sp*s , si = S .rel-*ₘ (sp*r , s) in
    sp*s , (ri , si)

  module _ {a b s t u} {M : LinMor s t} {N : LinMor t u} where

    _>>AsLinRel_ : AsLinRel M a → AsLinRel N b → AsLinRel (M >>LinMor N) (a ⊔ b)
    (R >>AsLinRel S) .linRel = R .linRel >>LinRel S .linRel
    (R >>AsLinRel S) .equiv = mk⇔
      (λ { (r , s) → ≤*-trans (S .equiv .to s) (N .hom-mono (R .equiv .to r)) })
      (λ le → R .equiv .from ≤*-refl , S .equiv .from le)

  0LinRel : ∀ {s t} → LinRel s t 0ℓ
  0LinRel .rel P Q = Q ≤0ₘ
  0LinRel .rel-≤ₘ xx yy le0 = 0ₘ-mono yy le0
  0LinRel .rel-0ₘ (sp0 , le0) = le0
  0LinRel .rel-+ₘ (sp+ , le0) = +ₘ-identity²← le0
  0LinRel .rel-*ₘ (sp* , le0) = *ₘ-annihilʳ← le0

  0AsLinRel : ∀ {s t} → AsLinRel {s} {t} 0ᴹ 0ℓ
  0AsLinRel .linRel = 0LinRel
  0AsLinRel .equiv = mk⇔ 0*→≤* ≤*→0*

  {-
  subLinRel : ∀ {s} → LinRel s s 0ℓ
  subLinRel .rel x x′ = x′ ≤* x
  subLinRel .rel-0ₘ (sp0 , sub) = 0ₘ-mono sub sp0
  subLinRel .rel-+ₘ (sp+ , sub) =
    ≤*-refl ↘, +ₘ-mono sub ≤*-refl ≤*-refl sp+ ,↙ ≤*-refl
  subLinRel .rel-*ₘ (sp* , sub) = *ₘ-mono sub ≤-refl ≤*-refl sp* , ≤*-refl
  -}

  [─]ᴿ : ∀ {u} → LinRel ε u 0ℓ
  [─]ᴿ .rel P Q = Q ≤0ₘ
  [─]ᴿ .rel-≤ₘ xx yy sp0 = 0ₘ-mono yy sp0
  [─]ᴿ .rel-0ₘ (sp , sp0) = sp0
  [─]ᴿ .rel-+ₘ (sp , sp0) = +ₘ-identity²← sp0
  [─]ᴿ .rel-*ₘ (sp , sp0) = *ₘ-annihilʳ← sp0

  [─]AsLinRel : ∀ {u} → AsLinRel {ε} {u} ([─]) _
  [─]AsLinRel .linRel = [─]ᴿ
  [─]AsLinRel .equiv = mk⇔ 0*→≤* ≤*→0*

  [_─_]ᴿ : ∀ {a b s t u} →
    LinRel s u a → LinRel t u b → LinRel (s <+> t) u (a ⊔ b)
  [ R ─ S ]ᴿ .rel P Q = R .rel (P ∘ ↙) ↘- Q ≤[_+ₘ_] -↙ S .rel (P ∘ ↘)
  [ R ─ S ]ᴿ .rel-≤ₘ (mk xx) yy (r ↘, r+s ,↙ s) =
    R .rel-≤ₘ (mk (xx ∘ ↙)) ≤*-refl r
    ↘, +ₘ-mono yy ≤*-refl ≤*-refl r+s ,↙
    S .rel-≤ₘ (mk (xx ∘ ↘)) ≤*-refl s
  [ R ─ S ]ᴿ .rel-0ₘ (sp0 , (r ↘, r+s ,↙ s)) =
    let sp0r , sp0s = un++ₙ sp0 in
    +ₘ-identity²→ (R .rel-0ₘ (sp0r , r) ↘, r+s ,↙ S .rel-0ₘ (sp0s , s))
  [ R ─ S ]ᴿ .rel-+ₘ (sp+ , (r ↘, r+s ,↙ s)) =
    let sp+r , sp+s = un++ₙ sp+ in
    let rl ↘, sp+r′ ,↙ rr = R .rel-+ₘ (sp+r , r) in
    let sl ↘, sp+s′ ,↙ sr = S .rel-+ₘ (sp+s , s) in
    let sp+r₂ ↘, l+r ,↙ sp+s₂ = +ₘ-inter (sp+r′ ↘, r+s ,↙ sp+s′) in
    (rl ↘, sp+r₂ ,↙ sl) ↘, l+r ,↙ (rr ↘, sp+s₂ ,↙ sr)
  [ R ─ S ]ᴿ .rel-*ₘ (sp* , (r ↘, r+s ,↙ s)) =
    let sp*r , sp*s = un++ₙ sp* in
    let sp*r′ , r′ = R .rel-*ₘ (sp*r , r) in
    let sp*s′ , s′ = S .rel-*ₘ (sp*s , s) in
    let sp*′ , l+r = *ₘ-distribʳ← (sp*r′ ↘, r+s ,↙ sp*s′) in
    sp*′ , (r′ ↘, l+r ,↙ s′)

  [_─_]AsLinRel : ∀ {a b s t u} {M : LinMor s u} {N : LinMor t u} →
    AsLinRel M a → AsLinRel N b → AsLinRel [ M ─ N ] (a ⊔ b)
  [ R ─ S ]AsLinRel .linRel = [ R .linRel ─ S .linRel ]ᴿ
  [ R ─ S ]AsLinRel .equiv = mk⇔
    (λ { (ll ↘, sp+ ,↙ rr) →
      ≤*-trans (+*→≤* sp+) (+*-mono (R .equiv .f ll) (S .equiv .f rr)) })
    (λ le → R .equiv .g ≤*-refl ↘, ≤*→+* le ,↙ S .equiv .g ≤*-refl)
    where
    open PoLeftSemimodule (Vᴾ _) renaming (+ₘ-mono to +*-mono)
    open Equivalence

  -- TODO: maybe Q′ should be a (linear) predicate on vectors, rather than
  -- a concrete vector.
  [─_─]ᴿ : ∀ {u} → Vector Ann u → LinRel [-] u 0ℓ
  [─ Q′ ─]ᴿ .rel P Q = Q ≤[ P here *ₘ Q′ ]
  [─ Q′ ─]ᴿ .rel-≤ₘ (mk xx) yy sp = *ₘ-mono yy (xx here) ≤*-refl sp
  [─ Q′ ─]ᴿ .rel-0ₘ (sp0 , sp) = *ₘ-annihilˡ→ (sp0 .get here , sp)
  [─ Q′ ─]ᴿ .rel-+ₘ (sp+ , sp) = *ₘ-distribˡ→ (sp+ .get here , sp)
  [─ Q′ ─]ᴿ .rel-*ₘ (sp* , sp) = *ₘ-assoc→ (sp* .get here , sp)

  [─_─]AsLinRel : ∀ {u} (Q′ : Vector Ann u) → AsLinRel [─ Q′ ─] 0ℓ
  [─ Q′ ─]AsLinRel .linRel = [─ Q′ ─]ᴿ
  [─ Q′ ─]AsLinRel .equiv = mk⇔ *ₗ→≤* ≤*→*ₗ

  [│]ᴿ : ∀ {s} → LinRel s ε 0ℓ
  [│]ᴿ .rel _ _ = ⊤
  [│]ᴿ .rel-≤ₘ _ _ _ = _
  [│]ᴿ .rel-0ₘ _ = []ₙ
  [│]ᴿ .rel-+ₘ _ = _↘,_,↙_ {left = []} {[]} _ []ₙ _
  [│]ᴿ .rel-*ₘ _ = _,_ {middle = []} []ₙ _

  [│]AsLinRel : ∀ {s} → AsLinRel ([│] {s = s}) 0ℓ
  [│]AsLinRel .linRel = [│]ᴿ
  [│]AsLinRel .equiv = mk⇔ (const []ₙ) _

  [_│_]ᴿ : ∀ {a b s t u} →
    LinRel s t a → LinRel s u b → LinRel s (t <+> u) (a ⊔ b)
  [ R │ S ]ᴿ .rel P Q = R .rel P (Q ∘ ↙) × S .rel P (Q ∘ ↘)
  [ R │ S ]ᴿ .rel-≤ₘ xx (mk yy) (ll , rr) =
    R .rel-≤ₘ xx (mk (yy ∘ ↙)) ll , S .rel-≤ₘ xx (mk (yy ∘ ↘)) rr
  [ R │ S ]ᴿ .rel-0ₘ (sp0 , (ll , rr)) =
    R .rel-0ₘ (sp0 , ll) ++ₙ S .rel-0ₘ (sp0 , rr)
  [ R │ S ]ᴿ .rel-+ₘ (sp+ , (ll , rr)) =
    let llR ↘, sp+R ,↙ rrR = R .rel-+ₘ (sp+ , ll) in
    let llS ↘, sp+S ,↙ rrS = S .rel-+ₘ (sp+ , rr) in
    _↘,_,↙_ {left = _ ++ _} {_ ++ _} (llR , llS) (sp+R ++ₙ sp+S) (rrR , rrS)
  [ R │ S ]ᴿ .rel-*ₘ (sp* , (ll , rr)) =
    let sp*R , llR = R .rel-*ₘ (sp* , ll) in
    let sp*S , rrS = S .rel-*ₘ (sp* , rr) in
    _,_ {middle = _ ++ _} (sp*R ++ₙ sp*S) (llR , rrS)

  [_│_]AsLinRel : ∀ {a b s t u} {M : LinMor s t} {N : LinMor s u} →
    AsLinRel M a → AsLinRel N b → AsLinRel [ M │ N ] (a ⊔ b)
  [ R │ S ]AsLinRel .linRel = [ R .linRel │ S .linRel ]ᴿ
  [ R │ S ]AsLinRel .equiv = mk⇔
    (λ (ll , rr) → R .equiv .f ll ++ₙ S .equiv .f rr)
    (λ le → let ll , rr = un++ₙ le in R .equiv .g ll , S .equiv .g rr)
    where open Equivalence

  [│_│]ᴿ : ∀ {s} → Vector Ann s → LinRel s [-] 0ℓ
  [│_│]ᴿ {[-]} P′ .rel P Q = Q here ≤[ P here * P′ here ]
  [│_│]ᴿ {ε} P′ .rel P Q = Q ≤0ₘ
  [│_│]ᴿ {sl <+> sr} P′ .rel P Q =
    [│ P′ ∘ ↙ │]ᴿ .rel (P ∘ ↙) ↘- Q ≤[_+ₘ_] -↙ [│ P′ ∘ ↘ │]ᴿ .rel (P ∘ ↘)
  [│_│]ᴿ {[-]} P′ .rel-≤ₘ (mk xx) (mk yy) r =
    *-mono↔ (yy here) (xx here) ≤-refl r
  [│_│]ᴿ {ε} P′ .rel-≤ₘ xx yy sp = 0ₘ-mono yy sp
  [│_│]ᴿ {sl <+> sr} P′ .rel-≤ₘ xx yy (l ↘, sp ,↙ r) =
    let xx↙ , xx↘ = un++ₙ xx in
    [│ P′ ∘ ↙ │]ᴿ .rel-≤ₘ xx↙ ≤*-refl l
    ↘, +ₘ-mono yy ≤*-refl ≤*-refl sp ,↙
    [│ P′ ∘ ↘ │]ᴿ .rel-≤ₘ xx↘ ≤*-refl r
  [│_│]ᴿ {[-]} P′ .rel-0ₘ (mk sp0 , r) = [ annihilˡ→ (sp0 here , r) ]ₙ
  [│_│]ᴿ {ε} P′ .rel-0ₘ (mk sp0 , sp) = sp
  [│_│]ᴿ {sl <+> sr} P′ .rel-0ₘ (mk sp0 , (l ↘, mk sp ,↙ r)) =
    let mk sp0l = [│ P′ ∘ ↙ │]ᴿ .rel-0ₘ (mk (sp0 ∘ ↙) , l) in
    let mk sp0r = [│ P′ ∘ ↘ │]ᴿ .rel-0ₘ (mk (sp0 ∘ ↘) , r) in
    [ +-identity²→ (sp0l here ↘, sp here ,↙ sp0r here) ]ₙ
  [│_│]ᴿ {[-]} P′ .rel-+ₘ (mk sp+ , r) =
    let ll ↘, sp+′ ,↙ rr = distribˡ→ (sp+ here , r) in
    _↘,_,↙_ {left = [ _ ]} {[ _ ]} ll [ sp+′ ]ₙ rr
  [│_│]ᴿ {ε} P′ .rel-+ₘ (mk sp+ , mk r) =
    let ll ↘, sp+′ ,↙ rr = +-identity²← (r here) in
    _↘,_,↙_ {left = [ _ ]} {[ _ ]} [ ll ]ₙ [ sp+′ ]ₙ [ rr ]ₙ
  [│_│]ᴿ {sl <+> sr} P′ .rel-+ₘ (mk sp+ , (l ↘, mk sp ,↙ r)) =
    let ll ↘, mk sp+l ,↙ rl = [│ P′ ∘ ↙ │]ᴿ .rel-+ₘ (mk (sp+ ∘ ↙) , l) in
    let lr ↘, mk sp+r ,↙ rr = [│ P′ ∘ ↘ │]ᴿ .rel-+ₘ (mk (sp+ ∘ ↘) , r) in
    let sp+l′ ↘, sp+′ ,↙ sp+r′ = +-inter↔ (sp+l here ↘, sp here ,↙ sp+r here) in
    _↘,_,↙_ {left = [ _ ]} {[ _ ]}
      (ll ↘, [ sp+l′ ]ₙ ,↙ lr) [ sp+′ ]ₙ (rl ↘, [ sp+r′ ]ₙ ,↙ rr)
  [│_│]ᴿ {[-]} P′ .rel-*ₘ (mk sp* , r) =
    let r′ , sp*′ = *-assoc→ (sp* here , r) in
    _,_ {middle = [ _ ]} [ r′ ]ₙ sp*′
  [│_│]ᴿ {ε} P′ .rel-*ₘ (mk sp* , mk sp) =
    let sp*′ , sp′ = annihilʳ← (sp here) in
    _,_ {middle = [ _ ]} [ sp*′ ]ₙ [ sp′ ]ₙ
  [│_│]ᴿ {sl <+> sr} P′ .rel-*ₘ (mk sp* , (l ↘, mk sp ,↙ r)) =
    let mk sp*l , l′ = [│ P′ ∘ ↙ │]ᴿ .rel-*ₘ (mk (sp* ∘ ↙) , l) in
    let mk sp*r , r′ = [│ P′ ∘ ↘ │]ᴿ .rel-*ₘ (mk (sp* ∘ ↘) , r) in
    let sp*′ , sp′ = distribʳ← (sp*l here ↘, sp here ,↙ sp*r here) in
    _,_ {middle = [ _ ]} [ sp*′ ]ₙ (l′ ↘, [ sp′ ]ₙ ,↙ r′)

  [│_│]AsLinRel : ∀ {s} (P′ : Vector Ann s) → AsLinRel [│ P′ │] 0ℓ
  [│ P′ │]AsLinRel .linRel = [│ P′ │]ᴿ
  [│ P′ │]AsLinRel .equiv = mk⇔ (f {P′ = P′}) (g {P′ = P′})
    where
    open Sum 0# _+_

    f : ∀ {s P Q P′} → [│ P′ │]ᴿ .rel P Q → Q ≤* [ (∑ {s} λ i → P i * P′ i) ]
    f {[-]} r = [ r ]ₙ
    f {ε} r = 0*→≤* r
    f {sl <+> sr} (ll ↘, sp+ ,↙ rr) =
      +*→≤* (+ₘ-mono ≤*-refl (f {sl} ll) (f {sr} rr) sp+)

    g : ∀ {s P Q P′} → Q ≤* [ (∑ {s} λ i → P i * P′ i) ] → [│ P′ │]ᴿ .rel P Q
    g {[-]} le = un[-]ₙ le
    g {ε} le = ≤*→0* le
    g {sl <+> sr} le = g {sl} ≤*-refl ↘, ≤*→+* le ,↙ g {sr} ≤*-refl
