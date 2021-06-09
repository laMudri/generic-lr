{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Po
open import Level using (0ℓ; suc; _⊔_)

module Generic.Linear.Algebra (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ) where

  open PoSemiring poSemiring
    renaming (Carrier to Ann
             ; _≤_ to _⊴_
             ; ≤-refl to ⊴-refl; ≤-trans to ⊴-trans; ≤-reflexive to ⊴-reflexive
             )

  open import Algebra.Po.Construct.Vector as APCV
    using (Vector-poLeftSemimodule; id-PoSemiringMor)
  open import Algebra.PoToRel
  open import Algebra.Relational renaming (_↘_↙_ to _↘-_-↙_)
  open import Algebra.Relational.Relation
  open import Data.LTree
  open import Data.LTree.Vector hiding (setoid)
  open import Data.LTree.Vector.Properties
  open import Data.Product
  open import Data.Unit
  open import Function
  open import Relation.Binary using (REL; _=[_]⇒_; _⇒_)
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

  open import Generic.Linear.Operations rawPoSemiring

  private
    variable
      s t : LTree
      P Q R : Vector Ann s

  ⊴*-refl : P ⊴* P
  ⊴*-refl .get i = ⊴-refl

  ⊴*-trans : P ⊴* Q → Q ⊴* R → P ⊴* R
  ⊴*-trans PQ QR .get i = ⊴-trans (PQ .get i) (QR .get i)

  ≈*-refl : P ≈* P
  ≈*-refl .get i = refl

  ≈*-trans : P ≈* Q → Q ≈* R → P ≈* R
  ≈*-trans PQ QR .get i = trans (PQ .get i) (QR .get i)

  ≈*-sym : P ≈* Q → Q ≈* P
  ≈*-sym PQ .get i = sym (PQ .get i)

  ⊴*-reflexive : P ≈* Q → P ⊴* Q
  ⊴*-reflexive PQ .get i = ⊴-reflexive (PQ .get i)

  +*-identity↖ : (P : Vector Ann s) → 0* +* P ⊴* P
  +*-identity↖ P .get _ = +.identity-→ .proj₁ _
  +*-identity↗ : (P : Vector Ann s) → P +* 0* ⊴* P
  +*-identity↗ P .get _ = +.identity-← .proj₂ _
  +*-identity↙ : (P : Vector Ann s) → P ⊴* 0* +* P
  +*-identity↙ P .get _ = +.identity-← .proj₁ _
  +*-identity↘ : (P : Vector Ann s) → P ⊴* P +* 0*
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

  Annᴿ : RelSemiring 0ℓ 0ℓ
  Annᴿ = poSemiring-to-relSemiring poSemiring

  Vᴿ : LTree → RelLeftSemimodule _ 0ℓ 0ℓ
  Vᴿ s = poLeftSemimodule-to-relLeftSemimodule (Vᴾ s)

  open RelSemiring Annᴿ renaming (+-comm to +-comm↔; +-inter to +-inter↔)
  private open module Dummy {s} = RelLeftSemimodule (Vᴿ s)

  LinRel : ∀ (s t : LTree) ℓ → Set _
  LinRel s t ℓ = RelLeftSemimoduleRel (Vᴿ s) (Vᴿ t) ℓ
  open RelLeftSemimoduleRel public

  record AsLinRel (M : LinMor s t) ℓ : Set (suc ℓ) where
    field
      linRel : LinRel s t ℓ
      equiv : ∀ {P Q} → linRel .rel P Q ⇔ Q ⊴* M .hom P
  open AsLinRel public
  open Equivalence public using () renaming (f to to; g to from)

  idLinRel : ∀ {s} → LinRel s s 0ℓ
  idLinRel .rel x x′ = x′ ⊴* x
  idLinRel .rel-0ₘ (sp0 , le) = ⊴*-trans le sp0
  idLinRel .rel-+ₘ (sp+ , le) = ⊴*-refl ↘, ⊴*-trans le sp+ ,↙ ⊴*-refl
  idLinRel .rel-*ₘ (sp* , le) = ⊴*-trans le sp* , ⊴*-refl

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
      (λ { (r , s) → ⊴*-trans (S .equiv .to s) (N .hom-mono (R .equiv .to r)) })
      (λ le → R .equiv .from ⊴*-refl , S .equiv .from le)

  0LinRel : ∀ {s t} → LinRel s t 0ℓ
  0LinRel .rel P Q = Q ≤0ₘ
  0LinRel .rel-0ₘ (sp0 , le0) = le0
  0LinRel .rel-+ₘ (sp+ , le0) = +ₘ-identity²← le0
  0LinRel .rel-*ₘ (sp* , le0) = *ₘ-annihilʳ← le0

  0AsLinRel : ∀ {s t} → AsLinRel {s} {t} 0ᴹ 0ℓ
  0AsLinRel .linRel = 0LinRel
  0AsLinRel .equiv = id⇔

  {-
  subLinRel : ∀ {s} → LinRel s s 0ℓ
  subLinRel .rel x x′ = x′ ⊴* x
  subLinRel .rel-0ₘ (sp0 , sub) = 0ₘ-mono sub sp0
  subLinRel .rel-+ₘ (sp+ , sub) =
    ⊴*-refl ↘, +ₘ-mono sub ⊴*-refl ⊴*-refl sp+ ,↙ ⊴*-refl
  subLinRel .rel-*ₘ (sp* , sub) = *ₘ-mono sub ⊴-refl ⊴*-refl sp* , ⊴*-refl
  -}

  [─]ᴿ : ∀ {u} → LinRel ε u 0ℓ
  [─]ᴿ .rel P Q = Q ≤0ₘ
  [─]ᴿ .rel-0ₘ (sp , sp0) = sp0
  [─]ᴿ .rel-+ₘ (sp , sp0) = +ₘ-identity²← sp0
  [─]ᴿ .rel-*ₘ (sp , sp0) = *ₘ-annihilʳ← sp0

  [─]AsLinRel : ∀ {u} → AsLinRel {ε} {u} ([─]) _
  [─]AsLinRel .linRel = [─]ᴿ
  [─]AsLinRel .equiv = id⇔

  [_─_]ᴿ : ∀ {a b s t u} →
    LinRel s u a → LinRel t u b → LinRel (s <+> t) u (a ⊔ b)
  [ R ─ S ]ᴿ .rel P Q = R .rel (P ∘ ↙) ↘- Q ≤[_+ₘ_] -↙ S .rel (P ∘ ↘)
  [ R ─ S ]ᴿ .rel-0ₘ (sp0 , (r ↘, r+s ,↙ s)) =
    let sp0r , sp0s = un++₂ sp0 in
    +ₘ-identity²→ (R .rel-0ₘ (sp0r , r) ↘, r+s ,↙ S .rel-0ₘ (sp0s , s))
  [ R ─ S ]ᴿ .rel-+ₘ (sp+ , (r ↘, r+s ,↙ s)) =
    let sp+r , sp+s = un++₂ sp+ in
    let rl ↘, sp+r′ ,↙ rr = R .rel-+ₘ (sp+r , r) in
    let sl ↘, sp+s′ ,↙ sr = S .rel-+ₘ (sp+s , s) in
    let sp+r₂ ↘, l+r ,↙ sp+s₂ = +ₘ-inter (sp+r′ ↘, r+s ,↙ sp+s′) in
    (rl ↘, sp+r₂ ,↙ sl) ↘, l+r ,↙ (rr ↘, sp+s₂ ,↙ sr)
  [ R ─ S ]ᴿ .rel-*ₘ (sp* , (r ↘, r+s ,↙ s)) =
    let sp*r , sp*s = un++₂ sp* in
    let sp*r′ , r′ = R .rel-*ₘ (sp*r , r) in
    let sp*s′ , s′ = S .rel-*ₘ (sp*s , s) in
    let sp*′ , l+r = *ₘ-distribʳ← (sp*r′ ↘, r+s ,↙ sp*s′) in
    sp*′ , (r′ ↘, l+r ,↙ s′)

  [_─_]AsLinRel : ∀ {a b s t u} {M : LinMor s u} {N : LinMor t u} →
    AsLinRel M a → AsLinRel N b → AsLinRel [ M ─ N ] (a ⊔ b)
  [ R ─ S ]AsLinRel .linRel = [ R .linRel ─ S .linRel ]ᴿ
  [ R ─ S ]AsLinRel .equiv = mk⇔
    (λ { (ll ↘, sp+ ,↙ rr) →
      ⊴*-trans sp+ (+*-mono (R .equiv .f ll) (S .equiv .f rr)) })
    (λ le → R .equiv .g ⊴*-refl ↘, le ,↙ S .equiv .g ⊴*-refl)
    where
    open PoLeftSemimodule (Vᴾ _) renaming (+ₘ-mono to +*-mono)
    open Equivalence

  -- TODO: maybe Q′ should be a (linear) predicate on vectors, rather than
  -- a concrete vector.
  [─_─]ᴿ : ∀ {u} → Vector Ann u → LinRel [-] u 0ℓ
  [─ Q′ ─]ᴿ .rel P Q = Q ≤[ P here *ₘ Q′ ]
  [─ Q′ ─]ᴿ .rel-0ₘ (sp0 , sp) = *ₘ-annihilˡ→ (sp0 .get here , sp)
  [─ Q′ ─]ᴿ .rel-+ₘ (sp+ , sp) = *ₘ-distribˡ→ (sp+ .get here , sp)
  [─ Q′ ─]ᴿ .rel-*ₘ (sp* , sp) = *ₘ-assoc→ (sp* .get here , sp)

  [─_─]AsLinRel : ∀ {u} (Q′ : Vector Ann u) → AsLinRel [─ Q′ ─] 0ℓ
  [─ Q′ ─]AsLinRel .linRel = [─ Q′ ─]ᴿ
  [─ Q′ ─]AsLinRel .equiv = id⇔

  [│]ᴿ : ∀ {s} → LinRel s ε 0ℓ
  [│]ᴿ .rel _ _ = ⊤
  [│]ᴿ .rel-0ₘ _ = []₂
  [│]ᴿ .rel-+ₘ _ = _↘,_,↙_ {left = []} {[]} _ []₂ _
  [│]ᴿ .rel-*ₘ _ = _,_ {middle = []} []₂ _

  [│]AsLinRel : ∀ {s} → AsLinRel ([│] {s = s}) 0ℓ
  [│]AsLinRel .linRel = [│]ᴿ
  [│]AsLinRel .equiv = mk⇔ (const []₂) _

  [_│_]ᴿ : ∀ {a b s t u} →
    LinRel s t a → LinRel s u b → LinRel s (t <+> u) (a ⊔ b)
  [ R │ S ]ᴿ .rel P Q = R .rel P (Q ∘ ↙) × S .rel P (Q ∘ ↘)
  [ R │ S ]ᴿ .rel-0ₘ (sp0 , (ll , rr)) =
    R .rel-0ₘ (sp0 , ll) ++₂ S .rel-0ₘ (sp0 , rr)
  [ R │ S ]ᴿ .rel-+ₘ (sp+ , (ll , rr)) =
    let llR ↘, sp+R ,↙ rrR = R .rel-+ₘ (sp+ , ll) in
    let llS ↘, sp+S ,↙ rrS = S .rel-+ₘ (sp+ , rr) in
    _↘,_,↙_ {left = _ ++ _} {_ ++ _} (llR , llS) (sp+R ++₂ sp+S) (rrR , rrS)
  [ R │ S ]ᴿ .rel-*ₘ (sp* , (ll , rr)) =
    let sp*R , llR = R .rel-*ₘ (sp* , ll) in
    let sp*S , rrS = S .rel-*ₘ (sp* , rr) in
    _,_ {middle = _ ++ _} (sp*R ++₂ sp*S) (llR , rrS)

  [_│_]AsLinRel : ∀ {a b s t u} {M : LinMor s t} {N : LinMor s u} →
    AsLinRel M a → AsLinRel N b → AsLinRel [ M │ N ] (a ⊔ b)
  [ R │ S ]AsLinRel .linRel = [ R .linRel │ S .linRel ]ᴿ
  [ R │ S ]AsLinRel .equiv = mk⇔
    (λ (ll , rr) → R .equiv .f ll ++₂ S .equiv .f rr)
    (λ le → let ll , rr = un++₂ le in R .equiv .g ll , S .equiv .g rr)
    where open Equivalence

  [│_│]ᴿ : ∀ {s} → Vector Ann s → LinRel s [-] 0ℓ
  [│_│]ᴿ {[-]} P′ .rel P Q = Q here ≤[ P here * P′ here ]
  [│_│]ᴿ {ε} P′ .rel P Q = Q ≤0ₘ
  [│_│]ᴿ {sl <+> sr} P′ .rel P Q =
    [│ P′ ∘ ↙ │]ᴿ .rel (P ∘ ↙) ↘- Q ≤[_+ₘ_] -↙ [│ P′ ∘ ↘ │]ᴿ .rel (P ∘ ↘)
  [│_│]ᴿ {[-]} P′ .rel-0ₘ (mk sp0 , r) = [ annihilˡ→ (sp0 here , r) ]₂
  [│_│]ᴿ {ε} P′ .rel-0ₘ (mk sp0 , sp) = sp
  [│_│]ᴿ {sl <+> sr} P′ .rel-0ₘ (mk sp0 , (l ↘, mk sp ,↙ r)) =
    let mk sp0l = [│ P′ ∘ ↙ │]ᴿ .rel-0ₘ (mk (sp0 ∘ ↙) , l) in
    let mk sp0r = [│ P′ ∘ ↘ │]ᴿ .rel-0ₘ (mk (sp0 ∘ ↘) , r) in
    [ +-identity²→ (sp0l here ↘, sp here ,↙ sp0r here) ]₂
  [│_│]ᴿ {[-]} P′ .rel-+ₘ (mk sp+ , r) =
    let ll ↘, sp+′ ,↙ rr = distribˡ→ (sp+ here , r) in
    _↘,_,↙_ {left = [ _ ]} {[ _ ]} ll [ sp+′ ]₂ rr
  [│_│]ᴿ {ε} P′ .rel-+ₘ (mk sp+ , mk r) =
    let ll ↘, sp+′ ,↙ rr = +-identity²← (r here) in
    _↘,_,↙_ {left = [ _ ]} {[ _ ]} [ ll ]₂ [ sp+′ ]₂ [ rr ]₂
  [│_│]ᴿ {sl <+> sr} P′ .rel-+ₘ (mk sp+ , (l ↘, mk sp ,↙ r)) =
    let ll ↘, mk sp+l ,↙ rl = [│ P′ ∘ ↙ │]ᴿ .rel-+ₘ (mk (sp+ ∘ ↙) , l) in
    let lr ↘, mk sp+r ,↙ rr = [│ P′ ∘ ↘ │]ᴿ .rel-+ₘ (mk (sp+ ∘ ↘) , r) in
    let sp+l′ ↘, sp+′ ,↙ sp+r′ = +-inter↔ (sp+l here ↘, sp here ,↙ sp+r here) in
    _↘,_,↙_ {left = [ _ ]} {[ _ ]}
      (ll ↘, [ sp+l′ ]₂ ,↙ lr) [ sp+′ ]₂ (rl ↘, [ sp+r′ ]₂ ,↙ rr)
  [│_│]ᴿ {[-]} P′ .rel-*ₘ (mk sp* , r) =
    let r′ , sp*′ = *-assoc→ (sp* here , r) in
    _,_ {middle = [ _ ]} [ r′ ]₂ sp*′
  [│_│]ᴿ {ε} P′ .rel-*ₘ (mk sp* , mk sp) =
    let sp*′ , sp′ = annihilʳ← (sp here) in
    _,_ {middle = [ _ ]} [ sp*′ ]₂ [ sp′ ]₂
  [│_│]ᴿ {sl <+> sr} P′ .rel-*ₘ (mk sp* , (l ↘, mk sp ,↙ r)) =
    let mk sp*l , l′ = [│ P′ ∘ ↙ │]ᴿ .rel-*ₘ (mk (sp* ∘ ↙) , l) in
    let mk sp*r , r′ = [│ P′ ∘ ↘ │]ᴿ .rel-*ₘ (mk (sp* ∘ ↘) , r) in
    let sp*′ , sp′ = distribʳ← (sp*l here ↘, sp here ,↙ sp*r here) in
    _,_ {middle = [ _ ]} [ sp*′ ]₂ (l′ ↘, [ sp′ ]₂ ,↙ r′)

  [│_│]AsLinRel : ∀ {s} (P′ : Vector Ann s) → AsLinRel [│ P′ │] 0ℓ
  [│ P′ │]AsLinRel .linRel = [│ P′ │]ᴿ
  [│ P′ │]AsLinRel .equiv = mk⇔ (f {P′ = P′}) (g {P′ = P′})
    where
    open Sum 0# _+_

    f : ∀ {s P Q P′} → [│ P′ │]ᴿ .rel P Q → Q ⊴* [ (∑ {s} λ i → P i * P′ i) ]
    f {[-]} r = [ r ]₂
    f {ε} r = r
    f {sl <+> sr} (ll ↘, sp+ ,↙ rr) =
      +ₘ-mono ⊴*-refl (f {sl} ll) (f {sr} rr) sp+

    g : ∀ {s P Q P′} → Q ⊴* [ (∑ {s} λ i → P i * P′ i) ] → [│ P′ │]ᴿ .rel P Q
    g {[-]} le = le .get here
    g {ε} le = le
    g {sl <+> sr} le = g {sl} ⊴*-refl ↘, le ,↙ g {sr} ⊴*-refl
